from makepage.utils import register_rule, render_step

@register_rule("rfl")
def rule_rfl(tactic, final_mark, proof):
    proof.tactic_counter["rfl"] += 1
    return render_step(
        tag = "显然",
        content = "该命题显然成立",
        final_mark = final_mark
    )