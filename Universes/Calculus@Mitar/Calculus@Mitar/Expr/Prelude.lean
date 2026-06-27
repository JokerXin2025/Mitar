import Lean2TeX.Register
import Batteries
import Aesop

macro "the" : term => `(some)

declare_aesop_rule_sets [InitializeExpr]
declare_aesop_rule_sets [ExprSimplify]
