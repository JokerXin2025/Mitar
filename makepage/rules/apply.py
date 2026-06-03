from makepage.utils import register_rule, render_step

@register_rule("apply")
def rule_apply(step, previous, subsequent, mark_list, proof):
    goal_before = previous.get("goal", "<code>goal_before</code>")
    goal_after = subsequent.get("goal", "<code>goal_after</code>")
    return render_step(
        tag = "应用结论",
        content = f"要证明{goal_before}, 只需证明{goal_after}即可",
        goal_before = goal_before,
        goal_after = goal_after,
        mark_list = mark_list
    )