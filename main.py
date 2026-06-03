import os.path, json, makepage.rules
from textwrap import indent
from makepage.utils import HANDLERS, TEMPLATE_BASE, TEMPLATE_PROOF, to_roman

PASS = 0
SORRY = 1
ERROR = 2

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
                html_blocks.append(f"<!-- Unknown Step: {step_id} -->")
        return "\n".join(html_blocks)
    def make(self, state = PASS):
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
                TEMPLATE_PROOF.substitute(
                    tag = tag,
                    title = title,
                    content = indent(self.render(self.data[i], ["Global"]), "        ")
                )
            )
        return TEMPLATE_BASE.substitute(
            proof_state = proof_state,
            proof_content = indent("\n\n".join(proof_list), "        ")
        )

def main():
    current_dir = os.path.dirname(os.path.abspath(__file__))
    json_path = os.path.join(current_dir, 'input.json')
    html_path = os.path.join(current_dir, 'output.html')
    try:
        with open(json_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
    except FileNotFoundError:
        print(f"未找到 {json_path} !")
        return
    engine = ProofEngine(data)
    with open(html_path, 'w', encoding='utf-8') as f:
        f.write(engine.make())
    print(f"已输出结果到 {html_path}")

if __name__ == "__main__":
    main()
