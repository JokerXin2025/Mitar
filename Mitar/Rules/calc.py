from Mitar.utils import register_rule
from Mitar.engine import render_cal_step
from Mitar.i18n import tr


def _rel_tex(proof, relation):
    """渲染 calc 链一步的关系符号。

    ProofScript 录制的 `relation` 字段是半应用的关系（如 `Eq Nat`，对应 Lean 的
    `getCalcRelation?` 的 `rel = e.appFn!.appFn!`），其头部常量就是关系本身；取
    `templates.toml` 的 `[[relation]]` 配置映射到符号（`Eq` → `=`、`LE.le` → `≤`）。
    """
    return proof.render_relation(relation)


@register_rule("calc")
def rule_calc(calc, previous, subsequent, mark_list, proof):
    init = calc.get("init")
    chain = calc.get("chain", [])
    if not isinstance(chain, list):
        chain = []
    calc_steps = []
    lhs = init
    for i, link in enumerate(chain):
        if not isinstance(link, dict):
            continue
        rhs = link.get("rhs")
        lhs_tex = proof.tex(lhs) if lhs is not None else ""
        rhs_tex = proof.tex(rhs) if rhs is not None else ""
        calc_steps.append(
            render_cal_step(
                tag = tr("strategy.calculation", proof.language) if i == 0 else "",
                lhs = lhs_tex if i == 0 else "",
                rel = _rel_tex(proof, link.get("relation")),
                rhs = rhs_tex,
                mark_list = mark_list if i == len(chain) - 1 else ["Independent"]
            )
        )
        lhs = rhs
    return "<div>" + "\n".join(calc_steps) + "</div>"
