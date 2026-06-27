import «Calculus@Mitar».Function.Differential.Defs
import «Calculus@Mitar».Function.Differential.Expr


/- ## 基本导数 Basic Derivatives -/

/-- ### 常数的导数（表达式）
    ### Constant's Derivative (Expression)
    Please use tactic `deriv` instead -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma DerivExpr.Const {x₀ L : ℝ}
  : D (fun _ ↦ L) x₀ = the 0
:= sorry

/-- ### 常数的左导数（表达式）
    ### Constant's Left Derivative (Expression)
    Please use tactic `deriv` instead -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma LeftDerivExpr.Const {x₀ L : ℝ}
  : D₋ (fun _ ↦ L) x₀ = the 0
:= sorry

/-- ### 常数的右导数（表达式）
    ### Constant's Right Derivative (Expression)
    Please use tactic `deriv` instead -/
@[aesop norm simp (rule_sets := [Derivative])]
lemma RightDerivExpr.Const {x₀ L : ℝ}
  : D₊ (fun _ ↦ L) x₀ = the 0
:= sorry


/- ## 导数运算法则 Derivative Calculation Rules -/

/-- ### 导数加法
    ### Derivative Addition -/
theorem Deriv.Add {F G : Function} {x₀ A B : ℝ}
    (h_f : Deriv F x₀ A) (h_g : Deriv G x₀ B)
  : Deriv (F + G) x₀ (A + B)
:= sorry

/-- ### 导数加法（表达式）
    ### Derivative Addition (Expression) -/
theorem DerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f + g) x₀ =? D f x₀ + D g x₀
:= sorry

/-- ### 左导数加法
    ### Left Derivative Addition -/
theorem LeftDeriv.Add {F G : Function} {x₀ A B : ℝ}
    (h_f : LeftDeriv F x₀ A) (h_g : LeftDeriv G x₀ B)
  : LeftDeriv (F + G) x₀ (A + B)
:= sorry

/-- ### 左导数加法（表达式）
    ### Left Derivative Addition (Expression) -/
theorem LeftDerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f + g) x₀ =? D₋ f x₀ + D₋ g x₀
:= sorry

/-- ### 右导数加法
    ### Right Derivative Addition -/
theorem RightDeriv.Add {F G : Function} {x₀ A B : ℝ}
    (h_f : RightDeriv F x₀ A) (h_g : RightDeriv G x₀ B)
  : RightDeriv (F + G) x₀ (A + B)
:= sorry

/-- ### 右导数加法（表达式）
    ### Right Derivative Addition (Expression) -/
theorem RightDerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f + g) x₀ =? D₊ f x₀ + D₊ g x₀
:= sorry

/-- ### 导数减法
    ### Derivative Subtraction -/
theorem Deriv.Sub {F G : Function} {x₀ A B : ℝ}
    (h_f : Deriv F x₀ A) (h_g : Deriv G x₀ B)
  : Deriv (F - G) x₀ (A - B)
:= sorry

/-- ### 导数减法（表达式）
    ### Derivative Subtraction (Expression) -/
theorem DerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f - g) x₀ =? D f x₀ - D g x₀
:= sorry

/-- ### 左导数减法
    ### Left Derivative Subtraction -/
theorem LeftDeriv.Sub {F G : Function} {x₀ A B : ℝ}
    (h_f : LeftDeriv F x₀ A) (h_g : LeftDeriv G x₀ B)
  : LeftDeriv (F - G) x₀ (A - B)
:= sorry

/-- ### 左导数减法（表达式）
    ### Left Derivative Subtraction (Expression) -/
theorem LeftDerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f - g) x₀ =? D₋ f x₀ - D₋ g x₀
:= sorry

/-- ### 右导数减法
    ### Right Derivative Subtraction -/
theorem RightDeriv.Sub {F G : Function} {x₀ A B : ℝ}
    (h_f : RightDeriv F x₀ A) (h_g : RightDeriv G x₀ B)
  : RightDeriv (F - G) x₀ (A - B)
:= sorry

/-- ### 右导数减法（表达式）
    ### Right Derivative Subtraction (Expression) -/
theorem RightDerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f - g) x₀ =? D₊ f x₀ - D₊ g x₀
:= sorry

/-- ### 导数乘法
    ### Derivative Multiplication -/
theorem Deriv.Mul {F G : Function} {x₀ A B : ℝ}
    (h_f : Deriv F x₀ A) (h_g : Deriv G x₀ B)
  : Deriv (F * G) x₀ (A * B)
:= sorry

/-- ### 导数乘法（表达式）
    ### Derivative Multiplication (Expression) -/
theorem DerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f * g) x₀ =? D f x₀ * D g x₀
:= sorry

/-- ### 左导数乘法
    ### Left Derivative Multiplication -/
theorem LeftDeriv.Mul {F G : Function} {x₀ A B : ℝ}
    (h_f : LeftDeriv F x₀ A) (h_g : LeftDeriv G x₀ B)
  : LeftDeriv (F * G) x₀ (A * B)
:= sorry

/-- ### 左导数乘法（表达式）
    ### Left Derivative Multiplication (Expression) -/
theorem LeftDerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f * g) x₀ =? D₋ f x₀ * D₋ g x₀
:= sorry

/-- ### 右导数乘法
    ### Right Derivative Multiplication -/
theorem RightDeriv.Mul {F G : Function} {x₀ A B : ℝ}
    (h_f : RightDeriv F x₀ A) (h_g : RightDeriv G x₀ B)
  : RightDeriv (F * G) x₀ (A * B)
:= sorry

/-- ### 右导数乘法（表达式）
    ### Right Derivative Multiplication (Expression) -/
theorem RightDerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f * g) x₀ =? D₊ f x₀ * D₊ g x₀
:= sorry

/-- ### 导数除法
    ### Derivative Division -/
theorem Deriv.Div {F G : Function} {x₀ A B : ℝ}
    (h_f : Deriv F x₀ A) (h_g : Deriv G x₀ B)
  : Deriv (F / G) x₀ (A / B)
:= sorry

/-- ### 导数除法（表达式）
    ### Derivative Division (Expression) -/
theorem DerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f / g) x₀ =? D f x₀ / D g x₀
:= sorry

/-- ### 左导数除法
    ### Left Derivative Division -/
theorem LeftDeriv.Div {F G : Function} {x₀ A B : ℝ}
    (h_f : LeftDeriv F x₀ A) (h_g : LeftDeriv G x₀ B)
  : LeftDeriv (F / G) x₀ (A / B)
:= sorry

/-- ### 左导数除法（表达式）
    ### Left Derivative Division (Expression) -/
theorem LeftDerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f / g) x₀ =? D₋ f x₀ / D₋ g x₀
:= sorry

/-- ### 右导数除法
    ### Right Derivative Division -/
theorem RightDeriv.Div {F G : Function} {x₀ A B : ℝ}
    (h_f : RightDeriv F x₀ A) (h_g : RightDeriv G x₀ B)
  : RightDeriv (F / G) x₀ (A / B)
:= sorry

/-- ### 右导数除法（表达式）
    ### Right Derivative Division (Expression) -/
theorem RightDerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f / g) x₀ =? D₊ f x₀ / D₊ g x₀
:= sorry
