include("compiler/ssair/ir.jl")
include("compiler/ssair/domtree.jl")
include("compiler/ssair/slot2ssa.jl")
include("compiler/ssair/queries.jl")
include("compiler/ssair/passes.jl")
include("compiler/ssair/verify.jl")
include("compiler/ssair/legacy.jl")

function normalize(expr)
    if isa(expr, Expr) && expr.head === :gotoifnot
        return GotoIfNot{Any}(expr.args...)
    elseif isa(expr, Expr) && expr.head === :return
        return ReturnNode{Any}(expr.args...)
    elseif isa(expr, LabelNode)
        return nothing
    end
    expr
end

function run_passes(ci::CodeInfo, mod::Module, nargs::Int)
    ci.code = copy(ci.code);
    foreach(1:length(ci.code)) do i
        ci.code[i] = normalize(ci.code[i]);
    end
    ci.code = strip_trailing_junk(ci.code);
    cfg = compute_basic_blocks(ci.code)
    defuse_insts = scan_slot_def_use(nargs, ci)
    domtree = construct_domtree(cfg)
    #ccall(:jl_, Cvoid, (Any,), domtree.idoms)
    #@Core.Main.Base.show domtree
    # @show ci.code
    ir = construct_ssa!(ci, mod, cfg, domtree, defuse_insts, nargs)
    #@Core.Main.Base.show ("pre_compact", ir)
    ir = compact!(ir)
    #@Core.Main.Base.show ("post_compact", ir)
    #ccall(:jl_, Cvoid, (Any,), ir.stmts)
    # @show ("pre_verify", ir)
    verify_ir(ir)
    #ir = predicate_insertion_pass!(ir, domtree)
    #ir = compact!(ir)
    #@show ("pre_getfield_elim", ir)
    #ir = getfield_elim_pass!(ir)
    #ir = compact!(ir)
    #@Core.Main.Base.show ("pre_lift", ir)
    #ccall(:jl_, Cvoid, (Any,), ir.stmts)
    ir = type_lift_pass!(ir)
    ir = compact!(ir)
    #ccall(:jl_, Cvoid, (Any,), ir.stmts)
    verify_ir(ir)
    ir
end
