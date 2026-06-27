import «Calculus@Mitar».Prelude


/-- ### Limit Expression Simplification
    __Usage__ `lim_simp`
    - `lim_simp` uses the following methods to simplify the limit expression
      (at most to a constant):
      - __Continuity__: Limit of a continuous function is the function value.
      - __Variable Substitution__: Rewrite the expression and `x₀` with
        the outer function and limit of the inner function
    - Only used for limit expression, such as `FuncLimitExpr`
-/
macro "lim_simp" : tactic => `(tactic|
  aesop (rule_sets := [ExprSimplify, LimitSimplify])
)
