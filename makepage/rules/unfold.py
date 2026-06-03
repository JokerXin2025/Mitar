from makepage.utils import register_rule, render_step

@register_rule("unfold")
def rule_unfold(step, previous, subsequent, mark_list, proof):
    goal_before = previous.get("goal", "<code>goal_before</code>")
    goal_after = subsequent.get("goal", "<code>goal_after</code>")
    concept = step.get("concept", "<code>concept</code>")
    h_before = step.get("at")
    if h_before:
        h_after = subsequent.get("unfold_at", "<code>h_after</code>")
        content = f"根据{concept}的定义, 我们有{h_after}"
    else:
        content = f"根据{concept}的定义, 我们需要证明{goal_after}"
    return render_step(
        tag = "应用定义",
        content = content,
        goal_before = goal_before,
        goal_after = goal_after,
        mark_list = mark_list
    )