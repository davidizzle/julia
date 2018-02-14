function stmt_effect_free(stmt, src, mod)
    isa(stmt, Union{PiNode, PhiNode}) && return true
    isa(stmt, Union{ReturnNode, PhiNode, GotoNode, GotoIfNot}) && return false
    statement_effect_free(stmt, src, mod)
end

function abstract_eval_ssavalue(s::SSAValue, src::IRCode)
    src.types[s.id]
end