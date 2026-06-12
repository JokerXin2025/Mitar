import «Calculus@Mitar».Function.Basic


/- # 函数极限 Function Limit -/

--  极限 | Limit
def FuncLimit (f : Function) (x₀ A : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ∈ Set.Ioo 0 δ → |f x - A| < ε

--  收敛 | Converges
def FuncConverges (f : Function) (x₀ : ℝ) : Prop :=
  ∃ A : ℝ, FuncLimit f x₀ A


/- # 函数极限的性质 Properties of Function Limit -/

--  唯一 | Unique
theorem FuncLimit_Unique {f : Function} {x₀ A B : ℝ}
    (hA : FuncLimit f x₀ A) (hB : FuncLimit f x₀ B) : A = B := by
  sorry

--  保号 | Sign-Preserving
theorem FuncLimit_pos {f : Function} {x₀ A : ℝ}
    (h_lim : FuncLimit f x₀ A) (h_A_pos : A > 0) :
    ∃ δ > 0, ∀ x, |x - x₀| ∈ Set.Ioo 0 δ → f x > 0 := by
  sorry
theorem FuncLimit_neg {f : Function} {x₀ A : ℝ}
    (h_lim : FuncLimit f x₀ A) (h_A_neg : A < 0) :
    ∃ δ > 0, ∀ x, |x - x₀| ∈ Set.Ioo 0 δ → f x < 0 := by
  sorry

--  收敛 => 局部有界 | Converges => Locally Bounded
theorem FuncConverges_LocallyBounded {f : Function} {x₀ : ℝ}
    (h : FuncConverges f x₀) : FuncLocallyBounded f x₀ := by
  sorry
