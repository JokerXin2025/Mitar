import os.path, json, textwrap, makepage.rules
from makepage.utils import HANDLERS, TEMPLATE_BASE

class ProofEngine:
    def __init__(self, data):
        self.data = data
        self.tactic_counter = dict.fromkeys(HANDLERS, 0)
    def render(self, data, mark_list):
        html_blocks = []
        for i in range(1, len(data) // 2 + 1):
            is_last_step = (i == len(data) // 2)
            mark = mark_list if is_last_step else []
            previous = data[2 * i - 2]
            is_strategy = data[2 * i - 1].get("strategy") if is_last_step else None
            if is_strategy:
                strategy = data[2 * i - 1]
                html_blocks.append(
                    HANDLERS.get(is_strategy)(strategy, previous, {}, mark, self)
                )
            else:
                step = data[2 * i - 1]
                tactic_id = step.get("step")
                subsequent = data[2 * i] if not is_last_step else {}
                handler = HANDLERS.get(tactic_id)
                if handler:
                    self.tactic_counter[tactic_id] += 1
                    html_blocks.append(
                        handler(step, previous, subsequent, mark, self)
                    )
                else:
                    html_blocks.append(f"<!-- Unknown Step: {tactic_id} -->")
        return "\n".join(html_blocks)

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
    content = engine.render(data, ["Global"])
    indented_content = textwrap.indent(f"\n{content}\n", "            ")
    output_html = TEMPLATE_BASE.substitute(
        content = indented_content
    )
    with open(html_path, 'w', encoding='utf-8') as f:
        f.write(output_html)
    print(f"已输出结果到 {html_path}")

if __name__ == "__main__":
    main()
