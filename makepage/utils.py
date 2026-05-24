import os.path
from string import Template

TACTIC_HANDLERS = {}

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_DIR = os.path.join(BASE_DIR, "templates")

def load_tpl(filename):
    path = os.path.join(TEMPLATE_DIR, filename)
    with open(path, "r", encoding="utf-8") as f:
        return Template(f.read())

TPL_STEP = load_tpl("step.html")
TPL_DETAILS = load_tpl("details.html")
TPL_STRATEGY = load_tpl("strategy.html")

def register_rule(name):
    def decorator(func):
        TACTIC_HANDLERS[name] = func
        return func
    return decorator

def render_step(tag, content, final_mark):
    if final_mark == "Global":
        final_mark = '\n   <span class="final-mark">$\\to$ 证毕</span>'
    elif final_mark == "Contradiction":
        final_mark = '\n    <span class="final-mark contradiction">$\\to$ 矛盾</span>'
    elif final_mark == "Induction":
        final_mark = '\n    <span class="final-mark induction">$\\to$ 完成</span>'
    else:
        final_mark = ""
    return TPL_STEP.substitute(
        tag = tag,
        content = content,
        final_mark = final_mark
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