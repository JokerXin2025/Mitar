from makepage.utils import register_rule, render_step

@register_rule("norm_num")
def rule_norm_num(tactic, final_mark, proof):
    proof.tactic_counter["norm_num"] += 1
    goal_before = tactic.get("goal", "<code>goal_before</code>")
    h_before = tactic.get("h")
    if final_mark:
        if goal_before == "矛盾":
            if h_before:
                content = f"算式 {h_before} 不成立"
            else:
                content = "通过数值计算获得矛盾"
        else:
            content = f"通过数值计算即可证明 {goal_before}"
    else:
        if h_before:
            h_after = tactic.get("h_", "<code>h_after</code>")
            content = f"通过计算可得 {h_after}"
        else:
            goal_after = tactic.get("goal_", "<code>goal_after</code>")
            content = f"目标可转化为 {goal_after}"
    return render_step(
        tag = "计算",
        content = content,
        final_mark = final_mark
    )