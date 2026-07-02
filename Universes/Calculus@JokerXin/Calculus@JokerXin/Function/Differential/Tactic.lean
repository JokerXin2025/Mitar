import «Calculus@JokerXin».Prelude
import «Calculus@JokerXin».Function.Differential.Rules
import «Calculus@JokerXin».Function.Differential.Elementary

open Lean Elab Tactic


/- ## Preparations !!! -/

@[aesop unsafe 80% tactic (rule_sets := [Derivative])]
def split_SMul : TacticM Unit := do
  evalTactic (← `(tactic| refine UdEqual.determine DerivExpr.SMul ?_))

@[aesop unsafe 80% tactic (rule_sets := [Derivative])]
def split_Add : TacticM Unit := do
  evalTactic (← `(tactic| refine UdEqual.determine DerivExpr.Add ?_))

@[aesop unsafe 80% tactic (rule_sets := [Derivative])]
def split_Sub : TacticM Unit := do
  evalTactic (← `(tactic| refine UdEqual.determine DerivExpr.Sub ?_))

@[aesop unsafe 80% tactic (rule_sets := [Derivative])]
def split_Mul : TacticM Unit := do
  evalTactic (← `(tactic| refine UdEqual.determine DerivExpr.Mul ?_))

@[aesop unsafe 80% tactic (rule_sets := [Derivative])]
def split_Div : TacticM Unit := do
  evalTactic (← `(tactic| refine UdEqual.determine DerivExpr.Div ?_))


/- ## Tactics -/

/-- ### Derivative Calculation
    __Usage__ `deriv`
    - `deriv` uses the following methods to calculate the derivative expression:
    - Only used for derivative expression, such as `DerivExpr`
-/
macro "deriv" : tactic => `(tactic|
  aesop (rule_sets := [ExprSimplify, Derivative])
)
