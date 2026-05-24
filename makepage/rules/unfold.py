from makepage.utils import register_rule, render_step

@register_rule("unfold")
def rule_unfold(tactic, final_mark, proof):
    proof.tactic_counter["unfold"] += 1
    h_before = tactic.get("h")
    concept = tactic.get("const", "<code>concept</code>")
    if h_before:
        h_after = tactic.get("h_", "<code>h_after</code>")
        content = f"根据 {concept} 的定义, 我们有 {h_after}"
    else:
        goal_after = tactic.get("goal_", "<code>goal_after</code>")
        content = f"根据 {concept} 的定义, 我们需要证明 {goal_after}"
    return render_step(
        tag = "应用定义",
        content = content,
        final_mark = final_mark
    )