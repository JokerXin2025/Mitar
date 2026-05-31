from makepage.utils import register_rule, render_step, render_details, render_strategy

@register_rule("Induction")
def rule_Induction(strategy, previous, subsequent, mark_list, proof):
    goal_init = previous.get("goal", "<code>goal_init</code>")
    n = strategy.get("on", "<code>n</code>")
    m = strategy.get("assume_on", "<code>m</code>")
    introduce_step = render_step(
        tag = "归纳对象",
        content = f"对自然数 ${n}$ 使用<span class='ref-link'>数学归纳法</span>",
        goal_before = goal_init,
        goal_after = "",
        mark_list = []
    )
    base_case_proof = proof.render(strategy.get("base_case_proof"), ["Induction"])
    base_case_details = render_details(
        open = True,
        tag = "基础情形",
        title = "验证命题对 $0$ 成立",
        line = True,
        content = f"\n{base_case_proof}\n"
    )
    inductive_proof = proof.render(strategy.get("inductive_proof"), mark_list.append("Induction"))
    inductive_details = render_details(
        open = True,
        tag = "归纳步骤",
        title = f"假设命题对 ${m}$ 成立, 下面证明命题对 ${m}+1$ 成立",
        line = True,
        content = f"\n{inductive_proof}\n"
    )
    return render_strategy(
        sort = "induction",
        tag = "数学归纳法",
        content = f"\n{introduce_step}\n\n{base_case_details}\n\n{inductive_details}\n"
    )