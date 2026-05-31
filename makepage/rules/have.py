from makepage.utils import register_rule, render_step, render_details

@register_rule("have")
def rule_have(step, previous, subsequent, mark_list, proof):
    goal_init = previous.get("goal", "<code>goal_init</code>")
    title = step.get("statement", "<code>title</code>")
    subproof = step.get("proof", {})
    proof_content = proof.render(subproof, mark_list.append("Local"))
    # `mark_list` is always `None`
    if not isinstance(subproof, list):
        return render_step(
            tag = "推导",
            content = f"由 {reason} 可知 {content}",
            goal_before = title,
            goal_after = "",
            mark_list = []
        )
    else:
        if len(subproof) == 2 and subproof[1].get("strategy"):
            return render_details(
                open = True,
                tag = "现在证明",
                title = title,
                line = False,
                content = f"\n{proof_content}\n"
            )
        else:
            if step.get("trivial"):
                return render_details(
                    open = True,
                    tag = "我们有",
                    title = title,
                    line = True,
                    content = f"\n{proof_content}\n"
                )
            else:
                return render_details(
                    open = False,
                    tag = "注意到",
                    title = title,
                    line = True,
                    content = f"\n{proof_content}\n"
            )