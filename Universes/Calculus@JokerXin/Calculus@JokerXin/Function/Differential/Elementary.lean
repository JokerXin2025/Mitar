import «Calculus@JokerXin».Function.Differential.Rules


/- ## 初等函数的导数 Elementary Functions' Derivatives -/

/-- ### 常函数的导数
    ### Constant Function's Derivative -/
lemma Constant_Deriv {C x₀ : ℝ}
  : Deriv (Constant C) x₀ 0
:= sorry

/-- ### 常函数的导数（表达式）
    ### Constant Function's Derivative (Expression) -/
lemma DerivExpr.Constant {C x₀ : ℝ}
  : D (fun _ ↦ C) x₀ = 0
:= sorry

/-- ### 常函数的左导数（表达式）
    ### Constant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Constant {C x₀ : ℝ}
  : D₋ (fun _ ↦ C) x₀ = 0
:= sorry

/-- ### 常函数的右导数（表达式）
    ### Constant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Constant {C x₀ : ℝ}
  : D₊ (fun _ ↦ C) x₀ = 0
:= sorry

/-- ### 恒等函数的导数
    ### Identity Function's Derivative -/
lemma Identity_Deriv {x₀ : ℝ}
  : Deriv Identity x₀ 1
:= sorry

/-- ### 恒等函数的导数（表达式）
    ### Identity Function's Derivative (Expression) -/
lemma DerivExpr.Identity {x₀ : ℝ}
  : D (·) x₀ = 1
:= sorry

/-- ### 恒等函数的左导数（表达式）
    ### Identity Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Identity {x₀ : ℝ}
  : D₋ (·) x₀ = 1
:= sorry

/-- ### 恒等函数的右导数（表达式）
    ### Identity Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Identity {x₀ : ℝ}
  : D₊ (·) x₀ = 1
:= sorry

/-- ### 绝对值函数的导数
    ### Absolute Value Function's Derivative -/
lemma Abs_Deriv {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : Deriv Abs x₀ (x₀ / |x₀|)
:= sorry

/-- ### 绝对值函数的导数（表达式）
    ### Absolute Value Function's Derivative (Expression) -/
lemma DerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D (|·|) x₀ = the (x₀ / |x₀|)
:= sorry

/-- ### 绝对值函数的左导数（表达式）
    ### Absolute Value Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ (|·|) x₀ = the (x₀ / |x₀|)
:= sorry

/-- ### 绝对值函数的右导数（表达式）
    ### Absolute Value Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Abs {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ (|·|) x₀ = the (x₀ / |x₀|)
:= sorry

/-- ### 幂函数的导数（对于 `x₀ < 0`）
    ### Power Function's Derivative (for `x₀ < 0`) -/
lemma Power_Deriv_neg {a x₀ : ℝ}
    (h_dom : x₀ < 0)
    (h_a : ∃ n : ℤ, a = ↑n)
  : Deriv (Power a) x₀ (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的导数（对于 `x₀ < 0`）（表达式）
    ### Power Function's Derivative (for `x₀ < 0`) (Expression) -/
lemma DerivExpr.Power_neg {a x₀ : ℝ}
    (h_dom : x₀ < 0)
    (h_a : ∃ n : ℤ, a = ↑n)
  : D (·^a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的左导数（对于 `x₀ < 0`）（表达式）
    ### Power Function's Left Derivative (for `x₀ < 0`) (Expression) -/
lemma LeftDerivExpr.Power_neg {a x₀ : ℝ}
    (h_dom : x₀ < 0)
    (h_a : ∃ n : ℤ, a = ↑n)
  : D₋ (·^a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的右导数（对于 `x₀ < 0`）（表达式）
    ### Power Function's Right Derivative (for `x₀ < 0`) (Expression) -/
lemma RightDerivExpr.Power_neg {a x₀ : ℝ}
    (h_dom : x₀ < 0)
    (h_a : ∃ n : ℤ, a = ↑n)
  : D₊ (·^a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的导数（对于 `x₀ > 0`）
    ### Power Function's Derivative (for `x₀ > 0`) -/
lemma Power_Deriv_pos {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : Deriv (Power a) x₀ (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的导数（对于 `x₀ > 0`）（表达式）
    ### Power Function's Derivative (for `x₀ > 0`) (Expression) -/
lemma DerivExpr.Power_pos {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D (·^a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的左导数（对于 `x₀ > 0`）（表达式）
    ### Power Function's Left Derivative (for `x₀ > 0`) (Expression) -/
lemma LeftDerivExpr.Power_pos {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ (·^a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的右导数（对于 `x₀ > 0`）（表达式）
    ### Power Function's Right Derivative (for `x₀ > 0`) (Expression) -/
lemma RightDerivExpr.Power_pos {a x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ (·^a) x₀ = the (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数在0处的右导数
    ### Power Function's Right Derivative at `0` -/
lemma Power_Deriv_0right {a : ℝ}
    (h_a : a > 0)
  : Deriv (Power a) 0 0
:= sorry

/-- ### 幂函数在0处的右导数（表达式）
    ### Power Function's Right Derivative at `0` (Expression) -/
lemma RightDerivExpr.Power_0right {a : ℝ}
    (h_a : a > 0)
  : D₊ (·^a) 0 = the 0
:= sorry

/-- ### 平方根函数的导数
    ### Square Root Function's Derivative -/
lemma Sqrt_Deriv {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : Deriv Sqrt x₀ (1 / (2 * √x₀))
:= sorry

/-- ### 平方根函数的导数（表达式）
    ### Square Root Function's Derivative (Expression) -/
lemma DerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D (√·) x₀ = the (1 / (2 * √x₀))
:= sorry

/-- ### 平方根函数的左导数（表达式）
    ### Square Root Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ (√·) x₀ = the (1 / (2 * √x₀))
:= sorry

/-- ### 平方根函数的右导数（表达式）
    ### Square Root Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sqrt {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ (√·) x₀ = the (1 / (2 * √x₀))
:= sorry

/-- ### 自然指数函数的导数
    ### Natural Exponential Function's Derivative -/
lemma Exp_Deriv {x₀ : ℝ}
  : Deriv Exp x₀ (exp x₀)
:= sorry

/-- ### 自然指数函数的导数（表达式）
    ### Natural Exponential Function's Derivative (Expression) -/
lemma DerivExpr.Exp {x₀ : ℝ}
  : D exp x₀ = the (exp x₀)
:= sorry

/-- ### 自然指数函数的左导数（表达式）
    ### Natural Exponential Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Exp {x₀ : ℝ}
  : D₋ exp x₀ = the (exp x₀)
:= sorry

/-- ### 自然指数函数的右导数（表达式）
    ### Natural Exponential Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Exp {x₀ : ℝ}
  : D₊ exp x₀ = the (exp x₀)
:= sorry

/-- ### 自然对数函数的导数
    ### Natural Logarithm Function's Derivative -/
lemma Ln_Deriv {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : Deriv Ln x₀ (1 / x₀)
:= sorry

/-- ### 自然对数函数的导数（表达式）
    ### Natural Logarithm Function's Derivative (Expression) -/
lemma DerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D ln x₀ = the (1 / x₀)
:= sorry

/-- ### 自然对数函数的左导数（表达式）
    ### Natural Logarithm Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₋ ln x₀ = the (1 / x₀)
:= sorry

/-- ### 自然对数函数的右导数（表达式）
    ### Natural Logarithm Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : D₊ ln x₀ = the (1 / x₀)
:= sorry

/-- ### 正弦函数的导数
    ### Sine Function's Derivative -/
lemma Sin_Deriv {x₀ : ℝ}
  : Deriv Sin x₀ (cos x₀)
:= sorry

/-- ### 正弦函数的导数（表达式）
    ### Sine Function's Derivative (Expression) -/
lemma DerivExpr.Sin {x₀ : ℝ}
  : D sin x₀ = the (cos x₀)
:= sorry

/-- ### 正弦函数的左导数（表达式）
    ### Sine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sin {x₀ : ℝ}
  : D₋ sin x₀ = the (cos x₀)
:= sorry

/-- ### 正弦函数的右导数（表达式）
    ### Sine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sin {x₀ : ℝ}
  : D₊ sin x₀ = the (cos x₀)
:= sorry

/-- ### 余弦函数的导数
    ### Cosine Function's Derivative -/
lemma Cos_Deriv {x₀ : ℝ}
  : Deriv Cos x₀ (- sin x₀)
:= sorry

/-- ### 余弦函数的导数（表达式）
    ### Cosine Function's Derivative (Expression) -/
lemma DerivExpr.Cos {x₀ : ℝ}
  : D cos x₀ = the (- sin x₀)
:= sorry

/-- ### 余弦函数的左导数（表达式）
    ### Cosine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Cos {x₀ : ℝ}
  : D₋ cos x₀ = the (- sin x₀)
:= sorry

/-- ### 余弦函数的右导数（表达式）
    ### Cosine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Cos {x₀ : ℝ}
  : D₊ cos x₀ = the (- sin x₀)
:= sorry

/-- ### 正切函数的导数
    ### Tangent Function's Derivative -/
lemma Tan_Deriv {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : Deriv Tan x₀ (sec x₀ ^2)
:= sorry

/-- ### 正切函数的导数（表达式）
    ### Tangent Function's Derivative (Expression) -/
lemma DerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D tan x₀ = the (sec x₀ ^2)
:= sorry

/-- ### 正切函数的左导数（表达式）
    ### Tangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₋ tan x₀ = the (sec x₀ ^2)
:= sorry

/-- ### 正切函数的右导数（表达式）
    ### Tangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Tan {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₊ tan x₀ = the (sec x₀ ^2)
:= sorry

/-- ### 余切函数的导数
    ### Cotangent Function's Derivative -/
lemma Cot_Deriv {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : Deriv Cot x₀ (- csc x₀ ^2)
:= sorry

/-- ### 余切函数的导数（表达式）
    ### Cotangent Function's Derivative (Expression) -/
lemma DerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D cot x₀ = the (- csc x₀ ^2)
:= sorry

/-- ### 余切函数的左导数（表达式）
    ### Cotangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₋ cot x₀ = the (- csc x₀ ^2)
:= sorry

/-- ### 余切函数的右导数（表达式）
    ### Cotangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Cot {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₊ cot x₀ = the (- csc x₀ ^2)
:= sorry

/-- ### 正割函数的导数
    ### Secant Function's Derivative -/
lemma Sec_Deriv {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : Deriv Sec x₀ (tan x₀ * sec x₀)
:= sorry

/-- ### 正割函数的导数（表达式）
    ### Secant Function's Derivative (Expression) -/
lemma DerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D sec x₀ = the (tan x₀ * sec x₀)
:= sorry

/-- ### 正割函数的左导数（表达式）
    ### Secant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₋ sec x₀ = the (tan x₀ * sec x₀)
:= sorry

/-- ### 正割函数的右导数（表达式）
    ### Secant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sec {x₀ : ℝ}
    (h_dom : cos x₀ ≠ 0)
  : D₊ sec x₀ = the (tan x₀ * sec x₀)
:= sorry

/-- ### 余割函数的导数
    ### Cosecant Function's Derivative -/
lemma Csc_Deriv {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : Deriv Csc x₀ (- cot x₀ * csc x₀)
:= sorry

/-- ### 余割函数的导数（表达式）
    ### Cosecant Function's Derivative (Expression) -/
lemma DerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D csc x₀ = the (- cot x₀ * csc x₀)
:= sorry

/-- ### 余割函数的左导数（表达式）
    ### Cosecant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₋ csc x₀ = the (- cot x₀ * csc x₀)
:= sorry

/-- ### 余割函数的右导数（表达式）
    ### Cosecant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Csc {x₀ : ℝ}
    (h_dom : sin x₀ ≠ 0)
  : D₊ csc x₀ = the (- cot x₀ * csc x₀)
:= sorry

/-- ### 双曲正弦函数的导数
    ### Hyp-Sine Function's Derivative -/
lemma Sinh_Deriv {x₀ : ℝ}
  : Deriv Sinh x₀ (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的导数（表达式）
    ### Hyp-Sine Function's Derivative (Expression) -/
lemma DerivExpr.Sinh {x₀ : ℝ}
  : D sinh x₀ = the (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的左导数（表达式）
    ### Hyp-Sine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sinh {x₀ : ℝ}
  : D₋ sinh x₀ = the (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的右导数（表达式）
    ### Hyp-Sine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sinh {x₀ : ℝ}
  : D₊ sinh x₀ = the (cosh x₀)
:= sorry

/-- ### 双曲余弦函数的导数
    ### Hyp-Cosine Function's Derivative -/
lemma Cosh_Deriv {x₀ : ℝ}
  : Deriv Cosh x₀ (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的导数（表达式）
    ### Hyp-Cosine Function's Derivative (Expression) -/
lemma DerivExpr.Cosh {x₀ : ℝ}
  : D cosh x₀ = the (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的左导数（表达式）
    ### Hyp-Cosine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Cosh {x₀ : ℝ}
  : D₋ cosh x₀ = the (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的右导数（表达式）
    ### Hyp-Cosine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Cosh {x₀ : ℝ}
  : D₊ cosh x₀ = the (sinh x₀)
:= sorry

/-- ### 双曲正切函数的导数
    ### Hyp-Tangent Function's Derivative -/
lemma Tanh_Deriv {x₀ : ℝ}
  : Deriv Tanh x₀ (sech x₀ ^2)
:= sorry

/-- ### 双曲正切函数的导数（表达式）
    ### Hyp-Tangent Function's Derivative (Expression) -/
lemma DerivExpr.Tanh {x₀ : ℝ}
  : D tanh x₀ = the (sech x₀ ^2)
:= sorry

/-- ### 双曲正切函数的左导数（表达式）
    ### Hyp-Tangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Tanh {x₀ : ℝ}
  : D₋ tanh x₀ = the (sech x₀ ^2)
:= sorry

/-- ### 双曲正切函数的右导数（表达式）
    ### Hyp-Tangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Tanh {x₀ : ℝ}
  : D₊ tanh x₀ = the (sech x₀ ^2)
:= sorry

/-- ### 双曲余切函数的导数
    ### Hyp-Cotangent Function's Derivative -/
lemma Coth_Deriv {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : Deriv Coth x₀ (- csch x₀ ^2)
:= sorry

/-- ### 双曲余切函数的导数（表达式）
    ### Hyp-Cotangent Function's Derivative (Expression) -/
lemma DerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D coth x₀ = the (- csch x₀ ^2)
:= sorry

/-- ### 双曲余切函数的左导数（表达式）
    ### Hyp-Cotangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ coth x₀ = the (- csch x₀ ^2)
:= sorry

/-- ### 双曲余切函数的右导数（表达式）
    ### Hyp-Cotangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Coth {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ coth x₀ = the (- csch x₀ ^2)
:= sorry

/-- ### 双曲正割函数的导数
    ### Hyp-Secant Function's Derivative -/
lemma Sech_Deriv {x₀ : ℝ}
  : Deriv Sech x₀ (- tanh x₀ * sech x₀)
:= sorry

/-- ### 双曲正割函数的导数（表达式）
    ### Hyp-Secant Function's Derivative (Expression) -/
lemma DerivExpr.Sech {x₀ : ℝ}
  : D sech x₀ = the (- tanh x₀ * sech x₀)
:= sorry

/-- ### 双曲正割函数的左导数（表达式）
    ### Hyp-Secant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Sech {x₀ : ℝ}
  : D₋ sech x₀ = the (- tanh x₀ * sech x₀)
:= sorry

/-- ### 双曲正割函数的右导数（表达式）
    ### Hyp-Secant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Sech {x₀ : ℝ}
  : D₊ sech x₀ = the (- tanh x₀ * sech x₀)
:= sorry

/-- ### 双曲余割函数的导数
    ### Hyp-Cosecant Function's Derivative -/
lemma Csch_Deriv {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : Deriv Csch x₀ (- coth x₀ * csch x₀)
:= sorry

/-- ### 双曲余割函数的导数（表达式）
    ### Hyp-Cosecant Function's Derivative (Expression) -/
lemma DerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D csch x₀ = the (- coth x₀ * csch x₀)
:= sorry

/-- ### 双曲余割函数的左导数（表达式）
    ### Hyp-Cosecant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₋ csch x₀ = the (- coth x₀ * csch x₀)
:= sorry

/-- ### 双曲余割函数的右导数（表达式）
    ### Hyp-Cosecant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Csch {x₀ : ℝ}
    (h_dom : x₀ ≠ 0)
  : D₊ csch x₀ = the (- coth x₀ * csch x₀)
:= sorry

/-- ### 反正弦函数的导数
    ### Arc-Sine Function's Derivative -/
lemma Arcsin_Deriv {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : Deriv Arcsin x₀ (1 / √(1 - x₀^2))
:= sorry

/-- ### 反正弦函数的导数（表达式）
    ### Arc-Sine Function's Derivative (Expression) -/
lemma DerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arcsin x₀ = the (1 / √(1 - x₀^2))
:= sorry

/-- ### 反正弦函数的左导数（表达式）
    ### Arc-Sine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arcsin x₀ = the (1 / √(1 - x₀^2))
:= sorry

/-- ### 反正弦函数的右导数（表达式）
    ### Arc-Sine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arcsin {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arcsin x₀ = the (1 / √(1 - x₀^2))
:= sorry

/-- ### 反余弦函数的导数
    ### Arc-Cosine Function's Derivative -/
lemma Arccos_Deriv {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : Deriv Arccos x₀ (-1 / √(1 - x₀^2))
:= sorry

/-- ### 反余弦函数的导数（表达式）
    ### Arc-Cosine Function's Derivative (Expression) -/
lemma DerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D arccos x₀ = the (-1 / √(1 - x₀^2))
:= sorry

/-- ### 反余弦函数的左导数（表达式）
    ### Arc-Cosine Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₋ arccos x₀ = the (-1 / √(1 - x₀^2))
:= sorry

/-- ### 反余弦函数的右导数（表达式）
    ### Arc-Cosine Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arccos {x₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
  : D₊ arccos x₀ = the (-1 / √(1 - x₀^2))
:= sorry

/-- ### 反正切函数的导数
    ### Arc-Tangent Function's Derivative -/
lemma Arctan_Deriv {x₀ : ℝ}
  : Deriv Arctan x₀ (1 / (1 + x₀^2))
:= sorry

/-- ### 反正切函数的导数（表达式）
    ### Arc-Tangent Function's Derivative (Expression) -/
lemma DerivExpr.Arctan {x₀ : ℝ}
  : D arctan x₀ = the (1 / (1 + x₀^2))
:= sorry

/-- ### 反正切函数的左导数（表达式）
    ### Arc-Tangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arctan {x₀ : ℝ}
  : D₋ arctan x₀ = the (1 / (1 + x₀^2))
:= sorry

/-- ### 反正切函数的右导数（表达式）
    ### Arc-Tangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arctan {x₀ : ℝ}
  : D₊ arctan x₀ = the (1 / (1 + x₀^2))
:= sorry

/-- ### 反余切函数的导数
    ### Arc-Cotangent Function's Derivative -/
lemma Arccot_Deriv {x₀ : ℝ}
  : Deriv Arccot x₀ (-1 / (1 + x₀^2))
:= sorry

/-- ### 反余切函数的导数（表达式）
    ### Arc-Cotangent Function's Derivative (Expression) -/
lemma DerivExpr.Arccot {x₀ : ℝ}
  : D arccot x₀ = the (-1 / (1 + x₀^2))
:= sorry

/-- ### 反余切函数的左导数（表达式）
    ### Arc-Cotangent Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arccot {x₀ : ℝ}
  : D₋ arccot x₀ = the (-1 / (1 + x₀^2))
:= sorry

/-- ### 反余切函数的右导数（表达式）
    ### Arc-Cotangent Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arccot {x₀ : ℝ}
  : D₊ arccot x₀ = the (-1 / (1 + x₀^2))
:= sorry

/-- ### 反正割函数的导数
    ### Arc-Secant Function's Derivative -/
lemma Arcsec_Deriv {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : Deriv Arcsec x₀ (1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反正割函数的导数（表达式）
    ### Arc-Secant Function's Derivative (Expression) -/
lemma DerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arcsec x₀ = the (1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反正割函数的左导数（表达式）
    ### Arc-Secant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arcsec x₀ = the (1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反正割函数的右导数（表达式）
    ### Arc-Secant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arcsec {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arcsec x₀ = the (1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反余割函数的导数
    ### Arc-Cosecant Function's Derivative -/
lemma Arccsc_Deriv {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : Deriv Arccsc x₀ (-1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反余割函数的导数（表达式）
    ### Arc-Cosecant Function's Derivative (Expression) -/
lemma DerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D arccsc x₀ = the (-1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反余割函数的左导数（表达式）
    ### Arc-Cosecant Function's Left Derivative (Expression) -/
lemma LeftDerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₋ arccsc x₀ = the (-1 / (|x₀| * √(x₀^2 - 1)))
:= sorry

/-- ### 反余割函数的右导数（表达式）
    ### Arc-Cosecant Function's Right Derivative (Expression) -/
lemma RightDerivExpr.Arccsc {x₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
  : D₊ arccsc x₀ = the (-1 / (|x₀| * √(x₀^2 - 1)))
:= sorry
