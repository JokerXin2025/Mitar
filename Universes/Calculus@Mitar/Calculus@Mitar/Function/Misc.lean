import «Calculus@Mitar».Prelude


/- # 邻域 Neighborhood -/

/-- ### 开邻域
    ### Open Neighborhood -/
abbrev Nbho (x₀ : ℝ) (δ : ℝ) : Set ℝ := Ioo (x₀ - δ) (x₀ + δ)

/-- ### 闭邻域
    ### Close Neighborhood -/
abbrev Nbhc (x₀ : ℝ) (δ : ℝ) : Set ℝ := Icc (x₀ - δ) (x₀ + δ)
