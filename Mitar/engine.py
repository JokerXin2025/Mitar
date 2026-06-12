from string import Template
from pathlib import Path
from textwrap import indent
from Mitar.utils import HANDLERS, to_roman

PASS = 0
SORRY = 1
ERROR = 2

CURRENT_DIR = Path(__file__).absolute().parent
TEMPLATE_STEP = Template((CURRENT_DIR / "Templates/step.html").read_text())
TEMPLATE_CAL_STEP = Template((CURRENT_DIR / "Templates/cal_step.html").read_text())
TEMPLATE_DETAILS = Template((CURRENT_DIR / "Templates/details.html").read_text())
TEMPLATE_STRATEGY = Template((CURRENT_DIR / "Templates/strategy.html").read_text())
TEMPLATE_PROOF = Template((CURRENT_DIR / "Templates/proof.html").read_text())
TEMPLATE_PAGE = Template((CURRENT_DIR / "Templates/page.html").read_text())


def render_step(tag, content, mark_list):
    final_mark = ""
    marks = mark_list.copy()
    while marks:
        mark = marks.pop()
        if mark == "Global" and len(mark_list) == 1:
            final_mark = '\n    <span class="final-mark">$\\to\\,$ 证毕</span>'
        elif mark == "Local" and len(mark_list) == 1:
            final_mark = '\n    <span class="final-mark"><i class="codicon codicon-check"></i></span>'
        elif mark == "Contradiction":
            final_mark += '\n    <span class="final-mark contradiction">$\\to\\,$ 矛盾</span>'
        elif mark == "Induction":
            final_mark += '\n    <span class="final-mark induction">$\\to\\,$ 完成</span>'
    return TEMPLATE_STEP.substitute(
        tag = tag,
        content = content,
        final_mark = final_mark
    )

def render_cal_step(tag, lhs, rel, rhs, mark_list):
    final_mark = ""
    marks = mark_list.copy()
    while marks:
        mark = marks.pop()
        if mark == "Global" and len(mark_list) == 1:
            final_mark = "\n    <span class=\"final-mark\">$\\to\\,$ 证毕</span>"
        elif mark == "Local" and len(mark_list) == 1:
            final_mark = "\n    <span class=\"final-mark\"><i class=\"codicon codicon-check\"></i></span>"
        elif mark == "Contradiction":
            final_mark += "\n    <span class=\"final-mark contradiction\">$\\to\\,$ 矛盾</span>"
        elif mark == "Induction":
            final_mark += "\n    <span class=\"final-mark induction\">$\\to\\,$ 完成</span>"
    return TEMPLATE_CAL_STEP.substitute(
        tag = tag,
        lhs = lhs,
        rel = rel,
        rhs = rhs,
        final_mark = final_mark
    )

def render_details(open, tag, title, content):
    return TEMPLATE_DETAILS.substitute(
        open = "open" if open else "close",
        tag = tag,
        title = title,
        content = indent(content, "        ")
    )

def render_strategy(sort, tag, content):
    return TEMPLATE_STRATEGY.substitute(
        sort = sort,
        tag = tag,
        content = indent(content, "        ")
    )

def render_proof(tag, title, content):
    return TEMPLATE_PROOF.substitute(
        tag = tag,
        title = title,
        content = indent(content, "        ")
    )

def render_page(proof_state, proof_content):
    return TEMPLATE_PAGE.substitute(
        source_path = str(Path.home() / ".Mitar") + "/",
        proof_state = proof_state,
        proof_content = indent(proof_content, "        ")
    )


class ProofEngine:

    def __init__(self, data):
        self.data = data
        self.tactic_counter = dict.fromkeys(HANDLERS, 0)

    def render(self, steps, mark_list):

        html_blocks = []
        for i in range(1, len(steps) // 2 + 1):

            is_last_step = (i == len(steps) // 2)
            mark = mark_list.copy() if is_last_step else []
            previous = steps[2 * i - 2]
            step = steps[2 * i - 1]
            step_id = step.get("name")
            subsequent = steps[2 * i] if not is_last_step else {}

            handler = HANDLERS.get(step_id)
            if handler:
                self.tactic_counter[step_id] += 1
                html_blocks.append(
                    handler(step, previous, subsequent, mark, self)
                )
            else:
                html_blocks.append(f"<!-- Silent Step: {step_id} -->")

        return "\n".join(html_blocks)

    def make(self, state=PASS):

        if state == PASS:
            proof_state = '<sup class="proof-mark pass"><i class="codicon codicon-check-all"></i></sup>'
        elif state == SORRY:
            proof_state = '<sup class="proof-mark sorry"><i class="codicon codicon-warning"></i></sup>'
        elif state == ERROR:
            proof_state = '<sup class="proof-mark error"><i class="codicon codicon-error"></i></sup>'

        proof_list = []
        for i in range(len(self.data)):

            if i == len(self.data) - 1:
                tag = "证明"
                tag_sort = "theorem"
                title = ""
            else:
                tag = f"引理 {to_roman(i+1)}"
                tag_sort = "lemma"
                title = "<span>" + self.data[i][0].get("goal", "") + "</span>"

            proof_list.append(
                render_proof(
                    tag = tag,
                    title = title,
                    content = self.render(self.data[i], ["Global"])
                )
            )

        return render_page(
            proof_state = proof_state,
            proof_content = "\n\n".join(proof_list)
        )
