from Mitar.utils import register_rule
from Mitar.engine import render_annotation


@register_rule("remark")
def rule_remark(remark, previous, subsequent, mark_list, proof):
    text = remark.get("text", "")
    return render_annotation(
        sort = "remark",
        icon = "<i class=\"codicon codicon-comment-discussion-quote\"></i>",
        content = text
    )
