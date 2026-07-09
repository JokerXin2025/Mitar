import «Calculus@JokerXin».Function.Concept
import «Calculus@JokerXin».Limit.Infinitesimal.Defs


/- ## 无穷小的性质 Properties of Infinitesimal -/

/-- ### 有界函数 × 无穷小
    ### Bounded Function × Infinitesimal -/
theorem Infinitesimal.MulBounded {F_b F_i : Function} {x₀ : ℝ}
    (h_bound : FuncBounded F_b)
    (h_ifs : isInfinitesimal F_i x₀)
  : isInfinitesimal (F_b * F_i) x₀
:= sorry

/-- ### 局部有界函数 × 无穷小
    ### Locally Bounded Function × Infinitesimal -/
theorem Infinitesimal.MulLocalBounded {F_b F_i : Function} {x₀ δ : ℝ}
    (h_bound : FuncLocalBounded F_b x₀ δ)
    (h_ifs : isInfinitesimal F_i x₀)
  : isInfinitesimal (F_b * F_i) x₀
:= sorry

/-- ### 无穷小 + 无穷小
    ### Infinitesimal + Infinitesimal -/
theorem Infinitesimal.Add {F G : Function} {x₀ : ℝ}
    (h_F : isInfinitesimal F x₀)
    (h_G : isInfinitesimal G x₀)
  : isInfinitesimal (F + G) x₀
:= sorry

/-- ### 无穷小 × 无穷小
    ### Infinitesimal × Infinitesimal -/
theorem Infinitesimal.Mul {F G : Function} {x₀ : ℝ}
    (h_F : isInfinitesimal F x₀)
    (h_G : isInfinitesimal G x₀)
  : isInfinitesimal (F * G) x₀
:= sorry

/-- ### 常函数 × 无穷小（表达式）
    ### Constant Function × Infinitesimal (Expression) -/
lemma Infinitesimal.MulConstant {f : ℝ → ℝ} {C x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (C • f) 0 = the 0
:= sorry

/-- ### 正弦函数 × 无穷小（表达式）
    ### Sine Function × Infinitesimal (Expression) -/
lemma Infinitesimal.MulSin {f : ℝ → ℝ} {x₀ : ℝ}
    (h_ifs : lim f x₀ = the 0)
  : lim (sin * f) 0 = the 0
:= sorry
