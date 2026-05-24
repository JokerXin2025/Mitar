import os.path, json, textwrap, makepage.rules
from makepage.utils import TACTIC_HANDLERS, load_tpl, render_step

class ProofEngine:
    def __init__(self, data):
        self.data = data
        self.tactic_counter = dict.fromkeys(TACTIC_HANDLERS, 0)
    def render(self, data, type):
        if not data: return ""
        if not data.get("use_tactic"):
            return render_step(
                tag = "推导",
                content = f"由 {reason} 可知 {content}",
                final_mark = None
            )
        else:
            tactics = data.get("tactics")
            html_blocks = []
            for i, tactic in enumerate(tactics):
                is_last_tactic = (i == len(tactics) - 1)
                final_mark = type if is_last_tactic else None
                handler = TACTIC_HANDLERS.get(tactic.get("by"))
                if handler:
                    html_blocks.append(handler(tactic, final_mark, self))
                else:
                    html_blocks.append(f"<!-- 未知操作: {tactic.get('by')} -->")
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
    inner_content = engine.render(data, "Global")
    indented_inner = textwrap.indent(f"\n{inner_content}\n", "            ")
    base_tpl = load_tpl("base.html")
    output_html = base_tpl.substitute(content=indented_inner)
    with open(html_path, 'w', encoding='utf-8') as f:
        f.write(output_html)
    print(f"已输出结果到 {html_path}")

if __name__ == "__main__":
    main()
