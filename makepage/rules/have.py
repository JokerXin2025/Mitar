import textwrap
from makepage.utils import TPL_DETAILS, register_rule, render_step

@register_rule("have")
def rule_have(tactic, final_mark, proof):
    proof.tactic_counter["have"] += 1
    content = tactic.get("content")
    subproof = proof.render(tactic.get("proof"), "Local")
    # `final_mark` is always `None`
    if not tactic.get("proof").get("use_tactic"):
        return render_step(
            tag = "推导",
            content = f"由 {reason} 可知 {content}",
            final_mark = None
        )
    else:
        if(len(tactic.get("proof").get("tactics", "")) == 1) and (
            tactic.get("proof").get("tactics")[0].get("is_strategy")
        ):
            return TPL_DETAILS.substitute(
                open_attr = "open",
                tag = "现在证明",
                title = content,
                line_class = "",
                content = textwrap.indent(f"\n{subproof}\n", "        ")
            )
        else:
            if tactic.get("trivial"):
                return TPL_DETAILS.substitute(
                    open_attr = "open",
                    tag = "我们有",
                    title = content,
                    line_class = " with-line",
                    content = textwrap.indent(f"\n{subproof}\n", "        ")
                )
            else:
                return TPL_DETAILS.substitute(
                    open_attr = "close",
                    tag = "注意到",
                    title = content,
                    line_class = " with-line",
                    content = textwrap.indent(f"\n{subproof}\n", "        ")
            )