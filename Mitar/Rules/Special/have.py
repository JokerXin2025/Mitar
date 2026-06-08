from Mitar.utils import register_rule
from Mitar.engine import render_step, render_details

@register_rule("have")
def rule_have(subgoal, previous, subsequent, mark_list, proof):
    # `mark_list` is always `None`
    _proof = subgoal.get("proof", {})
    if isinstance(_proof, dict):
        goal = _proof.get("goal", "<code>goal</code>")
        theorem = _proof.get("theorem")
        return render_step(
            tag = "推导",
            content = f"由<span class=\"ref-link\">{theorem}</span>可知{goal}",
            mark_list = ["Independent"]
        )
    else:
        proof_title = _proof[0].get("goal", "<code>title</code>")
        proof_content = proof.render(_proof, ["Local"])
        if subgoal.get("trivial"):
            return render_details(
                open = False,
                tag = "注意到",
                title = proof_title,
                content = proof_content
            )
        else:
            return render_details(
                open = True,
                tag = "我们有",
                title = proof_title,
                content = proof_content
            )
