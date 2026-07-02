import «Calculus@JokerXin».Prelude


/- # 邻域 Neighborhood -/

/-- ### 邻域
    ### Neighborhood -/
abbrev Nbho (x₀ δ : ℝ) : Set ℝ := Ioo (x₀ - δ) (x₀ + δ)

/-- ### 去心邻域
    ### Deleted Neighborhood -/
abbrev Nbhd (x₀ δ : ℝ) : Set ℝ := Ioo (x₀ - δ) x₀ ∪ Ioo x₀ (x₀ + δ)

/-- ### 去心邻域 ⊆ 邻域 -/
lemma Nbhd_subset_Nbho {x₀ δ : ℝ}
  : Nbhd x₀ δ ⊆ Nbho x₀ δ
:= sorry
