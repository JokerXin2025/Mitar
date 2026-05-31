from os.path import dirname, abspath, join
from textwrap import indent
from string import Template

BASE_DIR = dirname(abspath(__file__))
TEMPLATE_DIR = join(BASE_DIR, "templates")

def load_template(filename):
    path = join(TEMPLATE_DIR, filename)
    with open(path, "r", encoding="utf-8") as f:
        return Template(f.read())

TEMPLATE_BASE = load_template("base.html")
TEMPLATE_STEP = load_template("step.html")
TEMPLATE_DETAILS = load_template("details.html")
TEMPLATE_STRATEGY = load_template("strategy.html")

HANDLERS = {}

def register_rule(name):
    def decorator(func):
        HANDLERS[name] = func
        return func
    return decorator

def render_step(tag, content, goal_before, goal_after, mark_list):
    final_mark = ""
    mark_count = len(mark_list)
    while mark_list:
        mark = mark_list.pop()
        if mark == "Global" and mark_count == 1:
            final_mark = '\n   <span class="final-mark">$\\to$ 证毕</span>'
        elif mark == "Local" and mark_count == 1:
            final_mark = '\n   <span class="final-mark"><i class="codicon codicon-check"></i></span>'
        elif mark == "Contradiction":
            final_mark += '\n    <span class="final-mark contradiction">$\\to$ 矛盾</span>'
        elif mark == "Induction":
            final_mark += '\n    <span class="final-mark induction">$\\to$ 完成</span>'
    return TEMPLATE_STEP.substitute(
        tag = tag,
        content = content,
        final_mark = final_mark
    )

def render_details(open, tag, title, line, content):
    return TEMPLATE_DETAILS.substitute(
        open = "open" if open else "close",
        tag = tag,
        title = title,
        line = " with-line" if line else "",
        content = indent(content, "        ")
    )

def render_strategy(sort, tag, content):
    return TEMPLATE_STRATEGY.substitute(
        sort = sort,
        tag = tag,
        content = indent(content, "        ")
    )

def to_roman(num):
    val = [10, 9, 5, 4, 1]
    syb = ["X", "IX", "V", "IV", "I"]
    roman_num = ''
    i = 0
    while num > 0:
        for _ in range(num // val[i]):
            roman_num += syb[i]
            num -= val[i]
        i += 1
    return roman_num