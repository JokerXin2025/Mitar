from makepage.utils import register_rule, render_step

@register_rule("gcongr")
def rule_gcongr(tactic, final_mark, proof):
    proof.tactic_counter["gcongr"] += 1
    goal_before = tactic.get("goal", "<code>goal_before</code>")
    if final_mark:
        content = f"不等式 {goal_before} 可通过对已知条件进行保序变换得到"
    else:
        goal_after = tactic.get("goal_", "<code>goal_after</code>")
        content = f"要证明 {goal_before} , 只需证明 {goal_after} 即可"
    return render_step(
        tag = "放缩",
        content = content,
        final_mark = final_mark
    )