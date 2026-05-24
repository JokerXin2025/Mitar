from makepage.utils import register_rule, render_step

@register_rule("apply")
def rule_apply(tactic, final_mark, proof):
    proof.tactic_counter["apply"] += 1
    goal_before = tactic.get("goal", "<code>goal_before</code>")
    goal_after = tactic.get("goal_", "<code>goal_after</code>")
    return render_step(
        tag = "应用结论",
        content = f"要证明 {goal_before} , 只需证明 {goal_after} 即可",
        final_mark = final_mark
    )