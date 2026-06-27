import «Calculus@Mitar».Limit.Defs


/- ## 函数连续性 Function's Continuity -/

/-- ### 在某处连续
    ### Continuous at Some Point -/
def isContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  FuncLimit F x₀ (F.map x₀)

/-- ### 处处连续
    ### Continuous Everywhere -/
def isContinuous (F : Function) : Prop :=
  ∀ x ∈ F.domain, FuncLimit F x (F.map x)


/- ## 函数连续性的性质 Properties of Function's Continuity -/

/-- ### 连续性的加法 Continuity's Addition -/
theorem Continuous.Add {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= sorry

/-- ### 连续性的减法 Continuity's Subtraction -/
theorem Continuous.Sub {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= sorry

/-- ### 连续性的乘法 Continuity's Multiplication -/
theorem Continuous.Mul {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= sorry

/-- ### 连续性的除法 Continuity's Division -/
theorem Continuous.Div {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀) (h_g_not0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= sorry

/-
lemma Const_isContinuous {C x₀ : ℝ}
  : isContinuousAt (fun _ ↦ C) x₀
:= sorry

lemma x_isContinuous {x₀ : ℝ}
  : isContinuousAt (fun x ↦ x) x₀
:= sorry

lemma Monomial_isContinuous {a : ℕ} {x₀ : ℝ}
  : isContinuousAt (fun x ↦ x^a) x₀
:= sorry

open Lean Elab Tactic in
def autoContinuous : TacticM Unit := do
  evalTactic (← `(tactic|
    first
    | exact Eq.trans Const_isContinuous (by norm_num)
    | exact Eq.trans x_isContinuous (by norm_num)
    | exact Eq.trans Monomial_isContinuous (by norm_num)
    | exact Eq.trans (FuncLimitExpr.toRight x_isContinuous) (by norm_num)
    | exact Eq.trans (FuncLimitExpr.toRight Monomial_isContinuous) (by norm_num)
  ))
-/
