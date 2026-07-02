import «Calculus@JokerXin».Expr.Prelude
import «Calculus@JokerXin».Expr.UndeterminedEqual
import Mathlib.Tactic.NormNum.Core

open Lean Elab Tactic


/- ## Preparations -/

@[aesop unsafe 75% tactic (rule_sets := [ExprSimplify])]
def apply_congArg : TacticM Unit := do
  evalTactic (← `(tactic| apply congrArg the))

@[aesop unsafe 50% tactic (rule_sets := [ExprSimplify])]
def exe_norm_num : TacticM Unit := do
  evalTactic (← `(tactic| norm_num))


/- ## Tactics -/

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
  refine UndeterminedEqual.determine ?_ rfl
})


/-- ### Expression Simplification
    __Usage__ `expr_simp`
-/
macro "expr_simp" : tactic => `(tactic| {
  aesop (rule_sets := [ExprSimplify])
})
