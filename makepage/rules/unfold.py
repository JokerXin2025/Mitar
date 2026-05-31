from makepage.utils import register_rule, render_step

"""

step
----------
step        : unfold
arg_1       : concept
arg_2?      : h_before

previous
----------
goal        : goal_before

subsequent
----------
goal(!final): goal_after
id_1(arg_2) : h_after

"""

@register_rule("unfold")
def rule_unfold(step, previous, subsequent, mark_list, proof):
    goal_before = previous.get("goal", "<code>goal_before</code>")
    goal_after = subsequent.get("goal", "<code>goal_after</code>")
    concept = step.get("arg_1", "<code>concept</code>")
    h_before = step.get("arg_2")
    if h_before:
        h_after = subsequent.get("id_1", "<code>h_after</code>")
        content = f"根据 {concept} 的定义, 我们有 {h_after}"
    else:
        content = f"根据 {concept} 的定义, 我们需要证明 {goal_after}"
    return render_step(
        tag = "应用定义",
        content = content,
        goal_before = goal_before,
        goal_after = goal_after,
        mark_list = mark_list
    )