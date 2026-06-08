from Mitar.utils import register_rule
from Mitar.engine import render_cal_step

@register_rule("calc")
def rule_calc(calc, previous, subsequent, mark_list, proof):
    # `mark_list` is always not `None`
    _calc_steps = calc.get("calc_steps", [])
    calc_steps = []
    for i, _calc_step in enumerate(_calc_steps):
        calc_steps.append(
            render_cal_step(
                tag = "计算" if i == 0 else "",
                lhs = _calc_step.get("lhs", "<code>lhs</code>") if i == 0 else "",
                rel = _calc_step.get("name", "<code>rel</code>"),
                rhs = _calc_step.get("rhs", "<code>rhs</code>"),
                mark_list = mark_list if i == len(_calc_steps) - 1 else ["Independent"]
            )
        )
    return "<div>" + "\n".join(calc_steps) + "</div>"
