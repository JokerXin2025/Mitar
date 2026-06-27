import «Calculus@Mitar».Function.Continuous.Defs
import «Calculus@Mitar».Function.Differential.Defs
import «Calculus@Mitar».Limit.Infinitesimal.Defs


/- ## 泰勒公式 Taylor's Formula -/

/-- ### 泰勒多项式
    ### Taylor Polynomial -/
noncomputable abbrev TaylorPolynomial (F : Function) (x₀ : ℝ) (N : ℕ) : Function :=
  ⟨fun x ↦ ∑ k ∈ range N, (((NthDiff k F).map x₀ / (k)!) * (x - x₀)^k), Iii⟩

/-- ### 带皮亚诺余项的泰勒展开式
    ### Taylor's Expansion with Peano Remainder Term -/
theorem TaylorExpansion_Peano {N : ℕ} {F : Function} {x₀ : ℝ}
    (h_deriv : isNthDerivableAt N F x₀)
  : ∃ R : Function,
      F = TaylorPolynomial F x₀ N + R
      ∧ isHigherInfinitesimal R.map (fun x ↦ x^N) x₀
:= sorry

/-- ### 带拉格朗日余项的泰勒展开式（对于 `x ≤ x₀`）
    ### Taylor's Expansion with Lagrange Remainder Term (for `x ≤ x₀`) -/
theorem TaylorExpansion_Lagrange_left {N : ℕ} {F : Function} {x₀ x : ℝ}
    (h_x₀ : x ≤ x₀)
    (h_deriv₁ : Icc x x₀ ⊆ (NthDiff N F).domain ∧ isContinuous (NthDiff N F))
    (h_deriv₂ : Ioo x x₀ ⊆ (NthDiff (N + 1) F).domain)
  : ∃ ξ ∈ Ioo x x₀,
      F = TaylorPolynomial F x₀ N +
      ⟨fun x ↦ (((NthDiff (N + 1) F).map ξ / (N + 1)!) * (x - x₀) ^ (N + 1)), Iii⟩
:= sorry

/-- ### 带拉格朗日余项的泰勒展开式（对于 `x > x₀`）
    ### Taylor's Expansion with Lagrange Remainder Term (for `x > x₀`) -/
theorem TaylorExpansion_Lagrange_right {N : ℕ} {F : Function} {x₀ x : ℝ}
    (h_x₀ : x > x₀)
    (h_deriv₁ : Icc x₀ x ⊆ (NthDiff N F).domain ∧ isContinuous (NthDiff N F))
    (h_deriv₂ : Ioo x₀ x ⊆ (NthDiff (N + 1) F).domain)
  : ∃ ξ ∈ Ioo x₀ x,
      F = TaylorPolynomial F x₀ N +
      ⟨fun x ↦ (((NthDiff (N + 1) F).map ξ / (N + 1)!) * (x - x₀) ^ (N + 1)), Iii⟩
:= sorry
