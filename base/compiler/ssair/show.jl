
function Base.show(io::IO, cfg::CFG)
    foreach(pairs(cfg.blocks)) do (idx, block)
        println("$idx\t=>\t", join(block.succs, ", "))
    end
end

print_ssa(io::IO, val) = isa(val, SSAValue) ? print(io, "%$(val.id)") : print(io, val)
function Base.show(io::IO, code::IRCode)
    used = IdSet{Int}()
    println(io, "Code")
    foreach(stmt->scan_ssa_use!(used, stmt), code.stmts)
    foreach(((_a,_b,node),)->scan_ssa_use!(used, node), code.new_nodes)
    if isempty(used)
        maxsize = 0
    else
        maxused = maximum(used)
        maxsize = length(string(maxused))
    end
    cfg = code.cfg
    max_bb_idx_size = length(string(length(cfg.blocks)))
    bb_idx = 1
    perm = sortperm(code.new_nodes, by = x->x[1])
    new_nodes_perm = Iterators.Stateful(perm)
    for (idx, stmt) in Iterators.enumerate(code.stmts)
        bbrange = cfg.blocks[bb_idx].stmts
        bb_pad = max_bb_idx_size - length(string(bb_idx))
        if idx != last(bbrange)
            if idx == first(bbrange)
                print(io, "$(bb_idx) ","─"^(1+bb_pad)," ")
            else
                print(io, "│  "," "^max_bb_idx_size)
            end
        end
        print_sep = false
        if idx == last(bbrange)
            print_sep = true
        end
        floop = true
        while !isempty(new_nodes_perm) && code.new_nodes[Base.peek(new_nodes_perm)][1] == idx
            node_idx = popfirst!(new_nodes_perm)
            _, typ, node = code.new_nodes[node_idx]
            node_idx += length(code.stmts)
            if print_sep
                if floop
                    print(io, "$(bb_idx) ","─"^(1+bb_pad)," ")
                else
                    print(io, "│  "," "^max_bb_idx_size)
                end
            end
            print_sep = true
            floop = false
            print_ssa_typ = !isa(node, PiNode) && node_idx in used
            Base.with_output_color(:yellow, io) do io′
                print_node(io′, node_idx, node, used, maxsize; color = false,
                    print_typ=!print_ssa_typ || (isa(node, Expr) && typ != node.typ))
            end
            if print_ssa_typ
                printstyled(io, "::$(typ)", color=:red)
            end
            println(io)
        end
        if print_sep
            if idx == first(bbrange) && floop
                print(io, "$(bb_idx) ","─"^(1+bb_pad)," ")
            else
                print(io, idx == last(bbrange) ? string("└", "─"^(1+max_bb_idx_size), " ") :
                    string("│  ", " "^max_bb_idx_size))
            end
        end
        if idx == last(bbrange)
            bb_idx += 1
        end
        typ = code.types[idx]
        print_ssa_typ = !isa(stmt, PiNode) && idx in used
        print_node(io, idx, stmt, used, maxsize,
            print_typ=!print_ssa_typ || (isa(stmt, Expr) && typ != stmt.typ))
        if print_ssa_typ
            printstyled(io, "::$(typ)", color=:red)
        end
        println(io)
    end
end
