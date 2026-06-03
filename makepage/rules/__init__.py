# __init__.py

# Special

from .have import rule_have
from .calc import rule_calc

# Tactic

from .rfl import rule_rfl
from .gcongr import rule_gcongr
from .change import rule_change
from .unfold import rule_unfold
from .omega import rule_omega
from .norm_num import rule_norm_num
from .linarith import rule_linarith
from .nlinarith import rule_nlinarith

# Strategy

from .Induction import rule_Induction
from .Contradiction import rule_Contradiction
from .Cases import rule_Cases