from Mitar.utils import register_rule
from Mitar.engine import render_cal_step
from Mitar.i18n import tr


@register_rule("infer")
def rule_infer(infer, previous, subsequent, mark_list, proof):
    init = infer.get("init")
    chain = infer.get("chain", [])
    infer_steps = []
    lhs = init
    for i, link in enumerate(chain):
        rhs = link.get("rhs")
        lhs_tex = proof.tex(lhs) if lhs is not None else ""
        rhs_tex = proof.tex(rhs) if rhs is not None else ""
        infer_steps.append(
            render_cal_step(
                tag = tr("strategy.inference", proof.language) if i == 0 else "",
                lhs = lhs_tex if i == 0 else "",
                rel = "\\ \\Longrightarrow\\ ",
                rhs = rhs_tex,
                mark_list = mark_list if i == len(chain) - 1 else ["Independent"]
            )
        )
        lhs = rhs
    return "<div>" + "\n".join(infer_steps) + "</div>"
