# __init__.py

from pathlib import Path

CURRENT_DIR = Path(__file__).absolute().parent


# Special

from .Special.have import rule_have
from .Special.calc import rule_calc


# Strategy

from .Strategy.Induction import rule_Induction
from .Strategy.Contradiction import rule_Contradiction
from .Strategy.Cases import rule_Cases


# Tactic

from .Tactics import tactic_register

def Initialize():
    tactic_register(CURRENT_DIR / "Tactics.toml")
