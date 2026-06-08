from Mitar.utils import register_rule
from Mitar.engine import render_step, render_details, render_strategy

@register_rule("Induction")
def rule_Induction(strategy, previous, subsequent, mark_list, proof):
    _info = strategy.get("info", {})
    _base = strategy.get("base", [])
    _inductive = strategy.get("inductive", [])
    n = _info.get("on", "<code>n</code>")
    inductive_m = _inductive[0].get("assume_on", "<code>inductive_m</code>")
    inductive_hypo = _inductive[0].get("assume_h", "<code>inductive_hypo</code>")
    introduce_step = render_step(
        tag = "归纳对象",
        content = f"对自然数{n}使用<span class='ref-link'>数学归纳法</span>",
        mark_list = []
    )
    base_case_proof = proof.render(_base, ["Induction"])
    base_case_details = render_details(
        open = True,
        tag = "基础情形",
        title = "验证命题对 $0$ 成立",
        content = base_case_proof
    )
    inductive_proof = proof.render(_inductive, mark_list + ["Induction"])
    inductive_details = render_details(
        open = True,
        tag = "归纳步骤",
        title = f"假设命题对{inductive_m}成立, 下面证明命题对{inductive_m} $\\!+1$ 成立",
        content = inductive_proof
    )
    return render_strategy(
        sort = "induction",
        tag = "数学归纳法",
        content = introduce_step + "\n\n" + base_case_details + "\n\n" + inductive_details
    )
