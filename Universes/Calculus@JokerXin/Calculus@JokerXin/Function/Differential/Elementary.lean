import «Calculus@JokerXin».Function.Differential.Expr


/- ## 初等函数导数表 Table of Elementary Derivatives -/

/-- ### 常函数的导数
    ### Constant Function's Derivative -/
lemma Deriv.Constant {L x₀ : ℝ}
  : Deriv (Constant L) x₀ 0
:= sorry

/-- ### 常函数的导数（表达式）
    ### Constant Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Constant {L x₀ : ℝ}
  : D (fun _ ↦ L) x₀ = the 0
:= sorry

/-- ### 常函数的左导数
    ### Constant Function's Left Derivative -/
lemma LeftDeriv.Constant {L x₀ : ℝ}
  : LeftDeriv (Constant L) x₀ 0
:= sorry

/-- ### 常函数的左导数（表达式）
    ### Constant Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Constant {L x₀ : ℝ}
  : D₋ (fun _ ↦ L) x₀ = the 0
:= sorry

/-- ### 常函数的右导数
    ### Constant Function's Right Derivative -/
lemma RightDeriv.Constant {L x₀ : ℝ}
  : RightDeriv (Constant L) x₀ 0
:= sorry

/-- ### 常函数的右导数（表达式）
    ### Constant Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Constant {L x₀ : ℝ}
  : D₊ (fun _ ↦ L) x₀ = the 0
:= sorry

/-- ### 恒等函数的导数
    ### Identity Function's Derivative -/
lemma Deriv.Identity {x₀ : ℝ}
  : Deriv Identity x₀ 1
:= sorry

/-- ### 恒等函数的导数（表达式）
    ### Identity Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Identity {x₀ : ℝ}
  : D (·) x₀ = the 1
:= sorry

/-- ### 恒等函数的左导数
    ### Identity Function's Left Derivative -/
lemma LeftDeriv.Identity {x₀ : ℝ}
  : LeftDeriv Identity x₀ 1
:= sorry

/-- ### 恒等函数的左导数（表达式）
    ### Identity Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Identity {x₀ : ℝ}
  : D₋ (·) x₀ = the 1
:= sorry

/-- ### 恒等函数的右导数
    ### Identity Function's Right Derivative -/
lemma RightDeriv.Identity {x₀ : ℝ}
  : RightDeriv Identity x₀ 1
:= sorry

/-- ### 恒等函数的右导数（表达式）
    ### Identity Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Identity {x₀ : ℝ}
  : D₊ (·) x₀ = the 1
:= sorry
/-
/-- ### 幂函数的导数
    ### Power Function's Derivative -/
lemma Deriv.Power {a x₀ : ℝ}
  : Deriv (Power a) x₀ (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的左导数
    ### Power Function's Left Derivative -/
lemma LeftDeriv.Power {a x₀ : ℝ}
  : LeftDeriv (Power a) x₀ (a * x₀ ^ (a - 1))
:= sorry

/-- ### 幂函数的右导数
    ### Power Function's Right Derivative -/
lemma RightDeriv.Power {a x₀ : ℝ}
  : RightDeriv (Power a) x₀ (a * x₀ ^ (a - 1))
:= sorry
-/
/-- ### 幂函数的导数（表达式）
    ### Power Function's Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Power {a x₀ : ℝ}
  : D (fun x ↦ x^a) x₀ = the a * the x₀ ^ the (a - 1)
:= sorry

/-- ### 幂函数的左导数（表达式）
    ### Power Function's Left Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Power {a x₀ : ℝ}
  : D₋ (fun x ↦ x^a) x₀ = the a * the x₀ ^ the (a - 1)
:= sorry

/-- ### 幂函数的右导数（表达式）
    ### Power Function's Right Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Power {a x₀ : ℝ}
  : D₊ (fun x ↦ x^a) x₀ = the a * the x₀ ^ the (a - 1)
:= sorry

/-- ### 自然指数函数的导数
    ### Natural Exponential Function's Derivative -/
lemma Deriv.Exp {x₀ : ℝ}
  : Deriv Exp x₀ (exp x₀)
:= sorry

/-- ### 自然指数函数的导数（表达式）
    ### Natural Exponential Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Exp {x₀ : ℝ}
  : D exp x₀ = the (exp x₀)
:= sorry

/-- ### 自然指数函数的左导数
    ### Natural Exponential Function's Left Derivative -/
lemma LeftDeriv.Exp {x₀ : ℝ}
  : LeftDeriv Exp x₀ (exp x₀)
:= sorry

/-- ### 自然指数函数的左导数（表达式）
    ### Natural Exponential Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Exp {x₀ : ℝ}
  : D₋ exp x₀ = the (exp x₀)
:= sorry

/-- ### 自然指数函数的右导数
    ### Natural Exponential Function's Right Derivative -/
lemma RightDeriv.Exp {x₀ : ℝ}
  : RightDeriv Exp x₀ (exp x₀)
:= sorry

/-- ### 自然指数函数的右导数（表达式）
    ### Natural Exponential Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Exp {x₀ : ℝ}
  : D₊ exp x₀ = the (exp x₀)
:= sorry

/-- ### 自然对数函数的导数
    ### Natural Logarithm Function's Derivative -/
lemma Deriv.Ln {x₀ : ℝ}
    (h_x₀_ne_0 : x₀ ≠ 0)
  : Deriv Ln x₀ (1 / x₀)
:= sorry

/-- ### 自然对数函数的导数（表达式）
    ### Natural Logarithm Function's Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Ln {x₀ : ℝ}
  : D log x₀ = the 1 / the x₀
:= sorry

/-- ### 自然对数函数的左导数
    ### Natural Logarithm Function's Left Derivative -/
lemma LeftDeriv.Ln {x₀ : ℝ}
    (h_x₀_ne_0 : x₀ ≠ 0)
  : LeftDeriv Ln x₀ (1 / x₀)
:= sorry

/-- ### 自然对数函数的左导数（表达式）
    ### Natural Logarithm Function's Left Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Ln {x₀ : ℝ}
  : D₋ log x₀ = the 1 / the x₀
:= sorry

/-- ### 自然对数函数的右导数
    ### Natural Logarithm Function's Right Derivative -/
lemma RightDeriv.Ln {x₀ : ℝ}
    (h_x₀_ne_0 : x₀ ≠ 0)
  : RightDeriv Ln x₀ (1 / x₀)
:= sorry

/-- ### 自然对数函数的右导数（表达式）
    ### Natural Logarithm Function's Right Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Ln {x₀ : ℝ}
  : D₊ log x₀ = the 1 / the x₀
:= sorry

/-- ### 正弦函数的导数
    ### Sine Function's Derivative -/
lemma Deriv.Sin {x₀ : ℝ}
  : Deriv Sin x₀ (cos x₀)
:= sorry

/-- ### 正弦函数的导数（表达式）
    ### Sine Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Sin {x₀ : ℝ}
  : D sin x₀ = the (cos x₀)
:= sorry

/-- ### 正弦函数的左导数
    ### Sine Function's Left Derivative -/
lemma LeftDeriv.Sin {x₀ : ℝ}
  : LeftDeriv Sin x₀ (cos x₀)
:= sorry

/-- ### 正弦函数的左导数（表达式）
    ### Sine Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Sin {x₀ : ℝ}
  : D₋ sin x₀ = the (cos x₀)
:= sorry

/-- ### 正弦函数的右导数
    ### Sine Function's Right Derivative -/
lemma RightDeriv.Sin {x₀ : ℝ}
  : RightDeriv Sin x₀ (cos x₀)
:= sorry

/-- ### 正弦函数的右导数（表达式）
    ### Sine Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Sin {x₀ : ℝ}
  : D₊ sin x₀ = the (cos x₀)
:= sorry

/-- ### 余弦函数的导数
    ### Cosine Function's Derivative -/
lemma Deriv.Cos {x₀ : ℝ}
  : Deriv Cos x₀ (- sin x₀)
:= sorry

/-- ### 余弦函数的导数（表达式）
    ### Cosine Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Cos {x₀ : ℝ}
  : D cos x₀ = the (- sin x₀)
:= sorry

/-- ### 余弦函数的左导数
    ### Cosine Function's Left Derivative -/
lemma LeftDeriv.Cos {x₀ : ℝ}
  : LeftDeriv Cos x₀ (- sin x₀)
:= sorry

/-- ### 余弦函数的左导数（表达式）
    ### Cosine Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Cos {x₀ : ℝ}
  : D₋ cos x₀ = the (- sin x₀)
:= sorry

/-- ### 余弦函数的右导数
    ### Cosine Function's Right Derivative -/
lemma RightDeriv.Cos {x₀ : ℝ}
  : RightDeriv Cos x₀ (- sin x₀)
:= sorry

/-- ### 余弦函数的右导数（表达式）
    ### Cosine Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Cos {x₀ : ℝ}
  : D₊ cos x₀ = the (- sin x₀)
:= sorry
/-
/-- ### 正切函数的导数（表达式）
    ### Tangent Function's Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Tan {x₀ : ℝ}
  : D tan x₀ = the (cos x₀)
:= sorry

/-- ### 正切函数的左导数（表达式）
    ### Tangent Function's Left Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Tan {x₀ : ℝ}
  : D₋ tan x₀ = the (cos x₀)
:= sorry

/-- ### 正切函数的右导数（表达式）
    ### Tangent Function's Right Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Tan {x₀ : ℝ}
  : D₊ tan x₀ = the (cos x₀)
:= sorry

/-- ### 余切函数的导数（表达式）
    ### Cotangent Function's Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Cot {x₀ : ℝ}
  : D cot x₀ = the (cos x₀)
:= sorry

/-- ### 余切函数的左导数（表达式）
    ### Cotangent Function's Left Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Cot {x₀ : ℝ}
  : D₋ cot x₀ = the (cos x₀)
:= sorry

/-- ### 余切函数的右导数（表达式）
    ### Cotangent Function's Right Derivative (Expression)
    - Note that there's no need to ensure the expression's validity here -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Cot {x₀ : ℝ}
  : D₊ cot x₀ = the (cos x₀)
:= sorry
-/
/-- ### 双曲正弦函数的导数
    ### Hyperbolic Sine Function's Derivative -/
lemma Deriv.Sinh {x₀ : ℝ}
  : Deriv Sinh x₀ (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的导数（表达式）
    ### Hyperbolic Sine Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Sinh {x₀ : ℝ}
  : D sinh x₀ = the (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的左导数
    ### Hyperbolic Sine Function's Left Derivative -/
lemma LeftDeriv.Sinh {x₀ : ℝ}
  : LeftDeriv Sinh x₀ (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的左导数（表达式）
    ### Hyperbolic Sine Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Sinh {x₀ : ℝ}
  : D₋ sinh x₀ = the (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的右导数
    ### Hyperbolic Sine Function's Right Derivative -/
lemma RightDeriv.Sinh {x₀ : ℝ}
  : RightDeriv Sinh x₀ (cosh x₀)
:= sorry

/-- ### 双曲正弦函数的右导数（表达式）
    ### Hyperbolic Sine Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Sinh {x₀ : ℝ}
  : D₊ sinh x₀ = the (cosh x₀)
:= sorry

/-- ### 双曲余弦函数的导数
    ### Hyperbolic Cosine Function's Derivative -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma Deriv.Cosh {x₀ : ℝ}
  : Deriv Cosh x₀ (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的导数（表达式）
    ### Hyperbolic Cosine Function's Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Cosh {x₀ : ℝ}
  : D cosh x₀ = the (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的左导数
    ### Hyperbolic Cosine Function's Left Derivative -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDeriv.Cosh {x₀ : ℝ}
  : LeftDeriv Cosh x₀ (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的左导数（表达式）
    ### Hyperbolic Cosine Function's Left Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Cosh {x₀ : ℝ}
  : D₋ cosh x₀ = the (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的右导数
    ### Hyperbolic Cosine Function's Right Derivative -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDeriv.Cosh {x₀ : ℝ}
  : RightDeriv Cosh x₀ (sinh x₀)
:= sorry

/-- ### 双曲余弦函数的右导数（表达式）
    ### Hyperbolic Cosine Function's Right Derivative (Expression) -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Cosh {x₀ : ℝ}
  : D₊ cosh x₀ = the (sinh x₀)
:= sorry
