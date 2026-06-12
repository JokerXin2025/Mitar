import tomllib
from string import Template
from pathlib import Path

CURRENT_DIR = Path(__file__).absolute().parent

MAP_CONDITION = {
    "Final": "mark_list",
    "NonFinal": "not mark_list",
    "Contra": "goal == '矛盾'",
    "atHypo": "h",
    "atGoal": "not h"
}

MAP_ARGS_BASIC = {
    "#{goal}": "{goal}",
    "#{goal'}": "{goal_}",
    "#{h}": "{h}",
    "#{h'}": "{h_}",
}

TPL_CONTENT = Template('''\
from Mitar.utils import register_rule
from Mitar.engine import render_step

@register_rule("${id}")
def rule_${id}(step, previous, subsequent, mark_list, proof):

    goal = previous.get("goal", "")
    goal_ = subsequent.get("goal", "")
    h = step.get("at", "")
    h_ = subsequent.get("last_at", "")
    content = ""

${codes}

    return render_step(
        tag = "${tag}",
        content = content,
        mark_list = mark_list
    )
''')


class Rules(list):

    def __init__(self, data):
        super().__init__(data)

    def traverse(self, table, path):
        for key, value in table.items():
            if isinstance(value, dict):
                self.traverse(value, path + (key,))
            elif key == "content":
                self.append((path, value))

    def reorder(self):
        self.sort(
            key = lambda x: len(x[0])
        )


def generate_codes(tactic: dict):

    lines = []
    map_args = MAP_ARGS_BASIC.copy()

    # Exclusive Arguments
    for arg in tactic.get("args", []):
        lines.append(
            f"    {arg} = step.get(\"{arg}\", \"\")"
        )
        map_args[f"#{{{arg}}}"] = f"{{{arg}}}"

    rules = Rules([])
    rules.traverse(tactic, ())
    rules.reorder()

    for condition_tuple, content in rules:
        for old, new in map_args.items():
            content = content.replace(old, new)
        conditions = " and ".join(
            ["True"] + [MAP_CONDITION.get(condition, "True") for condition in condition_tuple]
        )
        lines.append(
            f"    if {conditions}:"
        )
        lines.append(
            f"        content = f'''{content}'''"
        )

    return "\n".join(lines)


def tactic_register(config_file: Path):

    with open(config_file, "rb") as dir_f:
        TACTIC_LIST = tomllib.load(dir_f)

    for tactic_info in TACTIC_LIST.get("Tactic", []):
        path = CURRENT_DIR / ".." / tactic_info.get("path")
        with open(path.resolve(), "rb") as rule_f:
            tactic = tomllib.load(rule_f)
        for id in tactic.get("id", []):
            exec_codes = TPL_CONTENT.substitute(
                id = id,
                tag = tactic.get("tag"),
                codes = generate_codes(tactic)
            )
            if __name__ == "__main__":
                print(f"\n--- {id} ---\n\n{exec_codes}")
            else:
                exec(exec_codes, globals())


if __name__ == "__main__":

    tactic_register(CURRENT_DIR / "../Tactics.toml")
