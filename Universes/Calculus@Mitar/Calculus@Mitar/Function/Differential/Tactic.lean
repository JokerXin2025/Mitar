import «Calculus@Mitar».Prelude


/-- ### Derivative Calculation
    __Usage__ `deriv`
    - `deriv` uses the following methods to calculate the derivative expression:
    - Only used for derivative expression, such as `DerivExpr`
-/
macro "deriv" : tactic => `(tactic|
  aesop (rule_sets := [ExprSimplify, Derivative])
)
