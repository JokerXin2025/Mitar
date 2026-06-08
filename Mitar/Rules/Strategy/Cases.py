from Mitar.utils import register_rule, to_roman
from Mitar.engine import render_step, render_details, render_strategy

@register_rule("Cases")
def rule_Cases(strategy, previous, subsequent, mark_list, proof):
    _info = strategy.get("info", {})
    _cases = strategy.get("cases", [])
    case_titles = []
    if _info.get("NaturalNumber"):
        # base on constructors of `Nat`
        n = _info.get("NaturalNumber")
        k = _cases[1][0].get("n-1")
        principle = f"自然数{n}要么为 $0$ , 要么作为某个自然数{k}的后继"
        case_titles.append(f"{n}$=0$")
        case_titles.append(f"{n}$=${k}$+1\\quad(\\,${k}$\\in\\mathbb N\\,)$")
    else:
        # base on some conclusion
        principle = _info.get("principle", "")
        for case in enumerate(_cases):
            case_titles.append("")
    principle_step = render_step(
        tag = "分类依据",
        content = principle,
        mark_list = []
    )
    content_list = [principle_step]
    for i, case in enumerate(_cases):
        content_list.append(
            render_details(
                open = True,
                tag = f"情形 {to_roman(i+1)}",
                title = case_titles[i],
                content = proof.render(case, mark_list)
            )
        )
    return render_strategy(
        sort = "cases",
        tag = "分类讨论",
        content = "\n\n".join(content_list)
    )
