from makepage.utils import register_rule, render_step, render_details

@register_rule("have")
def rule_have(subgoal, previous, subsequent, mark_list, proof):
    # `mark_list` is always `None`
    _proof = subgoal.get("proof", [])
    title = _proof[0].get("goal", "<code>title</code>")
    proof_content = proof.render(_proof, ["Local"])
    if not isinstance(_proof, list):
        return render_step(
            tag = "推导",
            content = f"由...可知{title}",
            goal_before = title,
            goal_after = "",
            mark_list = ["Independent"]
        )
    else:
        if subgoal.get("trivial"):
            return render_details(
                open = False,
                tag = "注意到",
                title = title,
                content = proof_content
            )
        else:
            return render_details(
                open = True,
                tag = "我们有",
                title = title,
                content = proof_content
            )