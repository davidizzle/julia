# Internal methods, only to be used to change to a different global interrupt handler
const _GLOBAL_INTERRUPT_ASYNC_CONDITION = Ref{Union{AsyncCondition,Nothing}}(nothing)
function _interrupt_wait()
    try
        # Wait to be interrupted
        wait(_GLOBAL_INTERRUPT_ASYNC_CONDITION[])
    catch err
        if err isa EOFError
            return false
        end
        if !(err isa InterruptException)
            rethrow(err)
        end
    end
    return true
end
function _interrupt_notify_all!()
    @lock INTERRUPT_HANDLERS_LOCK begin
        for (mod, handlers) in INTERRUPT_HANDLERS
            for (cond, handler) in handlers
                if handler === current_task()
                    @lock cond begin
                        notify(cond)
                    end
                end
            end
        end
    end
end
function _interrupt_notify_one!(handler::Task)
    cond = _find_interrupt_handler_condition(handler)
    @lock cond notify(cond)
end
function _throwto_interrupt!(task::Task)
    if task.state == :runnable
        task._isexception = true
        task.result = InterruptException()
        try
            schedule(task)
        catch
        end
    end
end

function _register_global_interrupt_handler(handler::Task)
    handler_ptr = Base.pointer_from_objref(handler)
    slot_ptr = cglobal(:jl_interrupt_handler, Ptr{Cvoid})
    Intrinsics.atomic_pointerset(slot_ptr, handler_ptr, :release)
end
function _unregister_global_interrupt_handler()
    slot_ptr = cglobal(:jl_interrupt_handler, Ptr{Cvoid})
    Intrinsics.atomic_pointerset(slot_ptr, C_NULL, :release)
end

const INTERRUPT_HANDLERS_LOCK = Threads.ReentrantLock()
const INTERRUPT_HANDLERS = Dict{Module,Vector{Pair{Task,Threads.Condition}}}()
const INTERRUPT_HANDLER_RUNNING = Threads.Atomic{Bool}(false)

"""
    register_interrupt_handler(mod::Module, handler::Task)

Registers the task `handler` to handle interrupts (such as from Ctrl-C).
Handlers are expected to call [`wait_for_interrupt`](@ref) and wait for it to
return. When it returns, an interrupt has been signalled, and the caller may
take whatever actions are necessary to gracefully interrupt any associated
running computations. It is recommended that the handler spawn tasks to perform
the graceful interrupt, so that the handler task may return quickly to again
calling `wait_for_interrupt` to remain responsive to future user interrupts.

When a Ctrl-C or manual SIGINT is received by the Julia process, one of two
actions may happen:

If the REPL is running, then the user will be presented with a terminal menu
which will allow them to do one of:
- Activate all interrupt handlers
- Activate all interrupt handlers for a specific module
- Force-interrupt the root task (`Base.roottask`)
- Ignore the interrupt (do nothing)
- Disable this interrupt handler logic (see below for details)
- Exit Julia gracefully (with `exit`)
- Exit Julia forcefully (with a `ccall` to `abort`)

If the REPL is not running (such as when running `julia myscript.jl`), then all
calls to `wait_for_interrupt` will return.

Note that if the interrupt handler logic is disabled by the above menu option,
Julia will fall back to the old Ctrl-C handling behavior, which has the
potential to cause crashes and undefined behavior (but can also interrupt more
kinds of code). If desired, the interrupt handler logic can be re-enabled by
calling `start_repl_interrupt_handler()`, which will disable the old Ctrl-C
handling behavior.

To unregister a previously-registered handler, use
[`unregister_interrupt_handler`](@ref).

!!! warn
    Non-yielding tasks may block interrupt handlers from running; this means
    that once an interrupt handler is registered, code like `while true end`
    may become un-interruptible without hitting Ctrl-C multiple times in rapid
    succession (which triggers a force-interrupt).
"""
function register_interrupt_handler(mod::Module, handler::Task)
    if ccall(:jl_generating_output, Cint, ()) == 1
        throw(ConcurrencyViolationError("Interrupt handlers cannot be registered during precompilation.\nPlease register your handler later (possibly in your module's `__init__`)."))
    end
    lock(INTERRUPT_HANDLERS_LOCK) do
        handlers = get!(Vector{Pair{Task,Threads.Condition}}, INTERRUPT_HANDLERS, mod)
        cond = Threads.Condition()
        push!(handlers, handler => cond)
    end
end

"""
    unregister_interrupt_handler(mod::Module, handler::Task)

Unregisters the interrupt handler task `handler`; see
[`register_interrupt_handler`](@ref) for further details.
"""
function unregister_interrupt_handler(mod::Module, handler::Task)
    if ccall(:jl_generating_output, Cint, ()) == 1
        throw(ConcurrencyViolationError("Interrupt handlers cannot be unregistered during precompilation."))
    end
    lock(INTERRUPT_HANDLERS_LOCK) do
        if !haskey(INTERRUPT_HANDLERS, mod)
            return false
        end
        handlers = INTERRUPT_HANDLERS[mod]
        deleteat!(handlers, findall(other->first(other) === handler, handlers))
    end
end

"""
    wait_for_interrupt()

Waits for an interrupt (Ctrl-C or SIGINT) to be signalled. The current task
must a registed interrupt handler (see [`register_interrupt_handler`](@ref)).
"""
function wait_for_interrupt()
    cond = _find_interrupt_handler_condition(current_task())
    @lock cond wait(cond)
end
function _find_interrupt_handler_condition(handler::Task)
    @lock INTERRUPT_HANDLERS_LOCK begin
        for (mod, handlers) in INTERRUPT_HANDLERS
            for (other_handler, cond) in handlers
                if handler === other_handler
                    return cond
                end
            end
        end
    end
    throw(ConcurrencyViolationError("This task is not a registered interrupt handler"))
end

function init_global_interrupt_handler!(force::Bool=false)
    if _GLOBAL_INTERRUPT_ASYNC_CONDITION[] === nothing || force
        cond = AsyncCondition()
        _GLOBAL_INTERRUPT_ASYNC_CONDITION[] = cond
        unsafe_store!(cglobal(:jl_interrupt_handler_condition, Ptr{Cvoid}), cond.handle)
    end
end

# Simple (no TUI) interrupt handler

function simple_interrupt_handler()
    last_time = 0.0
    while true
        _interrupt_wait() || return

        # Force-interrupt root task if two interrupts in quick succession (< 1s)
        now_time = time()
        diff_time = now_time - last_time
        last_time = now_time
        if diff_time < 1
            println("Force-interrupting...")
            _throwto_interrupt!(Base.roottask)
        else
            println("Interrupting...")
        end

        # Interrupt all handlers
        _interrupt_notify_all!()
    end
end
function simple_interrupt_handler_checked()
    try
        simple_interrupt_handler()
    catch err
        # Some internal error, make sure we start a new handler
        Threads.atomic_xchg!(INTERRUPT_HANDLER_RUNNING, false)
        _unregister_global_interrupt_handler()
        start_simple_interrupt_handler()
        rethrow()
    end
    # Clean exit
    Threads.atomic_xchg!(INTERRUPT_HANDLER_RUNNING, false)
    _unregister_global_interrupt_handler()
end
function start_simple_interrupt_handler(; force::Bool=false)
    if (Threads.atomic_cas!(INTERRUPT_HANDLER_RUNNING, false, true) == false) || force
        init_global_interrupt_handler!(force)
        simple_interrupt_handler_task = errormonitor(Threads.@spawn simple_interrupt_handler_checked())
        _register_global_interrupt_handler(simple_interrupt_handler_task)
    end
end

# REPL (TUI) interrupt handler

function repl_interrupt_handler()
    invokelatest(REPL_MODULE_REF[]) do REPL
        TerminalMenus = REPL.TerminalMenus

        root_menu = TerminalMenus.RadioMenu(
            [
             "Interrupt all",
             "Interrupt only...",
             "Interrupt root task (REPL/script)",
             "Ignore it",
             "Stop handling interrupts",
             "Exit Julia",
             "Force-exit Julia",
            ]
        )

        while true
            _interrupt_wait() || return

            # Display root menu
            @label display_root
            choice = TerminalMenus.request("Interrupt received, select an action:", root_menu)
            if choice == 1
                _interrupt_notify_all!()
            elseif choice == 2
                # Display modules menu
                mods = lock(INTERRUPT_HANDLERS_LOCK) do
                    collect(keys(INTERRUPT_HANDLERS))
                end
                mod_menu = TerminalMenus.RadioMenu(vcat(map(string, mods), "Go Back"))
                @label display_mods
                choice = TerminalMenus.request("Select a library to interrupt:", mod_menu)
                if choice > length(mods) || choice == -1
                    @goto display_root
                else
                    lock(INTERRUPT_HANDLERS_LOCK) do
                        for handler in INTERRUPT_HANDLERS[mods[choice]]
                            _interrupt_notify_one!(handler)
                        end
                    end
                    @goto display_mods
                end
            elseif choice == 3
                # Force-interrupt root task
                _throwto_interrupt!(Base.roottask)
            elseif choice == 4 || choice == -1
                # Do nothing
            elseif choice == 5
                # Exit handler (caller will unregister us)
                return
            elseif choice == 6
                # Exit Julia cleanly
                exit()
            elseif choice == 7
                # Force an exit
                ccall(:abort, Cvoid, ())
            end
        end
    end
end
function repl_interrupt_handler_checked()
    try
        repl_interrupt_handler()
    catch err
        # Some internal error, make sure we start a new handler
        Threads.atomic_xchg!(INTERRUPT_HANDLER_RUNNING, false)
        _unregister_global_interrupt_handler()
        start_repl_interrupt_handler()
        rethrow()
    end
    # Clean exit
    Threads.atomic_xchg!(INTERRUPT_HANDLER_RUNNING, false)
    _unregister_global_interrupt_handler()
end
function start_repl_interrupt_handler(; force::Bool=false)
    if (Threads.atomic_cas!(INTERRUPT_HANDLER_RUNNING, false, true) == false) || force
        init_global_interrupt_handler!(force)
        repl_interrupt_handler_task = errormonitor(Threads.@spawn repl_interrupt_handler_checked())
        _register_global_interrupt_handler(repl_interrupt_handler_task)
    end
end
