import Lean2TeX.Register
import Aesop.Frontend.Command

macro "the" : term => `(some)

declare_aesop_rule_sets [InitializeExpr]
declare_aesop_rule_sets [ExprSimplify]
