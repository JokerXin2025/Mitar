# __init__.py

# Strategy

from .Induction import rule_induction
from .Contradiction import rule_contradiction
from .Cases import rule_cases

# Step

from .have import rule_have

from .rfl import rule_rfl
from .gcongr import rule_gcongr
from .change import rule_change
from .unfold import rule_unfold
from .omega import rule_omega
from .norm_num import rule_norm_num
from .linarith import rule_linarith
from .nlinarith import rule_nlinarith