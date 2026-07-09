import «Calculus@JokerXin».Function.Continuity.Defs
import «Calculus@JokerXin».Function.Differential.Defs


/- ## 中值定理 Mean Value Theorems -/

/-- ### 费马引理
    ### Fermat Lemma -/
theorem Fermat_Lemma {F : Function} {x₀ δ : ℝ}
    (h_dom : Nbho x₀ δ ⊆ F.domain)
    (h_deriv : isDerivableAt F x₀)
    (h_extre : ∀ x ∈ Nbho x₀ δ, F.map x ≤ F.map x₀
               ∨ ∀ x ∈ Nbho x₀ δ, F.map x ≥ F.map x₀)
  : Deriv F x₀ 0
:= sorry

/-- ### 罗尔中值定理
    ### Rolle Mean Value Theorem -/
theorem Rolle_MeanValue {F : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_eq : F.map a = F.map b)
    (h_cont : isContinuousInIcc F a b)
    (h_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
  : ∃ ξ ∈ Ioo a b,
      Deriv F ξ 0
:= sorry

/-- ### 拉格朗日中值定理
    ### Lagrange Mean Value Theorem -/
theorem Lagrange_MeanValue {F : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_cont : isContinuousInIcc F a b)
    (h_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
  : ∃ ξ ∈ Ioo a b,
      Deriv F ξ ((F.map b - F.map a) / (b - a))
:= sorry

/-- ### 柯西中值定理
    ### Cauchy Mean Value Theorem -/
theorem Cauchy_MeanValue {F G : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_g'_ne_0 : ∀ x ∈ (Diff G).domain, (Diff G).map x ≠ 0)
    (h_F_cont : isContinuousInIcc F a b)
    (h_G_cont : isContinuousInIcc G a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
    (h_G_deriv : ∀ x ∈ Ioo a b, isDerivableAt G x)
  : ∃ ξ ∈ Ioo a b,
      (F.map b - F.map a) / (G.map b - G.map a) = (Diff F).map ξ / (Diff G).map ξ
:= sorry

/-- ### 柯西中值定理（乘积形式）
    ### Cauchy Mean Value Theorem (Product Form) -/
theorem Cauchy_MeanValue' {F G : Function} {a b : ℝ}
    (h_a_lt_b : a < b)
    (h_F_cont : isContinuousInIcc F a b)
    (h_G_cont : isContinuousInIcc G a b)
    (h_F_deriv : ∀ x ∈ Ioo a b, isDerivableAt F x)
    (h_G_deriv : ∀ x ∈ Ioo a b, isDerivableAt G x)
  : ∃ ξ ∈ Ioo a b,
      (Diff F).map ξ * (G.map b - G.map a) = (Diff G).map ξ * (F.map b - F.map a)
:= sorry
