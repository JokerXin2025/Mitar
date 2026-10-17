# __init__.py

from pathlib import Path

CURRENT_DIR = Path(__file__).absolute().parent


# Special

from .have import rule_have
from .calc import rule_calc
from .infer import rule_infer
from .diagram import rule_svg
from .remark import rule_remark
from .admit import rule_admit
from .embed import rule_embed


# Strategy

from Mitar.strategy import register_strategies


# Tactic

from Mitar.tactic import register_generic_tactics, tactic_register_dir


def Initialize():
    """Load built-in Strategy and Tactic configurations."""

    register_strategies()
    tactic_register_dir(CURRENT_DIR.parent / "Tactic")
    register_generic_tactics()
