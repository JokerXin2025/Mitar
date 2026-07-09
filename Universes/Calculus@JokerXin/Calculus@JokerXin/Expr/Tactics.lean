import «Calculus@JokerXin».Expr.Defs


/- ## Preparations -/

open Lean.Elab.Tactic in
@[aesop unsafe 50% tactic (rule_sets := [ExprSimplify])]
def apply_congArg : TacticM Unit := do
  evalTactic (← `(tactic| apply congrArg the))

open Lean.Elab.Tactic in
@[aesop unsafe 20% tactic (rule_sets := [ExprSimplify])]
private def exe_field : TacticM Unit := do
  evalTactic (← `(tactic| field))

private class AutoEval (expr : Option ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → expr = the val

instance eval_the {A : ℝ}
  : AutoEval (the A) A True where
  eq := directly rfl

instance eval_add {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoEval A a c₁] [h₂ : AutoEval B b c₂]
  : AutoEval (A + B) (a + b) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_a, h_b⟩
    rw [h₁.eq h_a, h₂.eq h_b]
    rfl

instance eval_sub {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoEval A a c₁] [h₂ : AutoEval B b c₂]
  : AutoEval (A - B) (a - b) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_a, h_b⟩
    rw [h₁.eq h_a, h₂.eq h_b]
    rfl

instance eval_mul {A B : Option ℝ} {a b : ℝ} {c₁ c₂ : Prop}
    [h₁ : AutoEval A a c₁] [h₂ : AutoEval B b c₂]
  : AutoEval (A * B) (a * b) (c₁ ∧ c₂) where
  eq := by
    intro ⟨h_a, h_b⟩
    rw [h₁.eq h_a, h₂.eq h_b]
    rfl

instance eval_div (A B : Option ℝ) (a b : ℝ) (c₁ c₂ : Prop)
    [h₁ : AutoEval A a c₁] [h₂ : AutoEval B b c₂]
  : AutoEval (A / B) (a / b) (c₁ ∧ c₂ ∧ b ≠ 0) where
  eq := by
    intro ⟨h_a, h_b, h_ne⟩
    rw [h₁.eq h_a, h₂.eq h_b]
    change (if the b = the 0 then none else _) = _
    have h_cond : the b ≠ the 0 := by simp [h_ne]
    rw [if_neg h_cond]
    rfl

/-
instance eval_pow (A B : Option ℝ) (a b : ℝ) (c₁ c₂ : Prop)
    [h₁ : AutoEval A a c₁] [h₂ : AutoEval B b c₂]
  : AutoEval (A ^ B) (a ^ b) (c₁ ∧ c₂ ∧ (a > 0 ∨ (a ≠ 0 ∧ b = 0))) where
  eq := by
    intro ⟨h_a, h_b, h_cond⟩
    rw [h₁.eq h_a, h₂.eq h_b]
    change (if a ≠ 0 ∧ b = 0 then the (1 : ℝ) else if a > 0 then the (a ^ b) else none) = _
    rcases h_cond with h_pos | ⟨ha_ne, hb_eq⟩
    · by_cases hb_zero : b = 0
      · have ha_ne_0 : a ≠ 0 := ne_of_gt h_pos
        simp [hb_zero, ha_ne_0]
      · simp [hb_zero, h_pos]
    · simp [ha_ne, hb_eq]
-/

@[aesop norm simp (rule_sets := [ExprSimplify])]
private lemma auto_eval (expr : Option ℝ) {val : ℝ} {cond : Prop}
    [AutoEval expr val cond] (h_cond : cond)
  : expr = the val := AutoEval.eq h_cond


/- ## Tactics -/

/-- ### Expression Initialization (`=`)
    __Usage__ `use_expr`
-/
macro "use_expr" : tactic => `(tactic|
  aesop (rule_sets := [InitializeExpr])
)

/-- ### Expression Simplification
    __Usage__ `expr_simp`
-/
macro "expr_simp" : tactic => `(tactic| {
  aesop (rule_sets := [ExprSimplify])
})
