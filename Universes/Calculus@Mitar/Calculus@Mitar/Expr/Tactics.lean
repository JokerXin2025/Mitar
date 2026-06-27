import «Calculus@Mitar».Expr.Prelude
import «Calculus@Mitar».Expr.UndeterminedEqual
import Mathlib.Tactic.NormNum.Core


open Lean Elab Tactic in
@[aesop safe tactic (rule_sets := [ExprSimplify])]
def ExprCongr : TacticM Unit := do
  evalTactic (← `(tactic| apply congrArg the))
  evalTactic (← `(tactic|
    first
    | assumption
    | norm_num
  ))


/-- ### Expression Initialization (`=`)
    __Usage__ `use_expr`
-/
macro "use_expr" : tactic => `(tactic|
  aesop (rule_sets := [InitializeExpr])
)


/-- ### Expression Initialization (`=?`)
    __Usage__ `use_expr'`
-/
macro "use_expr'" : tactic => `(tactic| {
  aesop (rule_sets := [InitializeExpr])
  apply (UndeterminedEqual_determine · rfl)
})


/-- ### Expression Simplification
    __Usage__ `expr_simp`
-/
macro "expr_simp" : tactic => `(tactic| {
  aesop (rule_sets := [ExprSimplify])
})
