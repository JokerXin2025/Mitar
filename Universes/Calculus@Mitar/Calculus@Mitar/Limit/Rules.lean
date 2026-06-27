import «Calculus@Mitar».Limit.Defs
import «Calculus@Mitar».Limit.Expr
import Lean.Elab.Tactic.Basic


/- ## 基本极限 Basic Limits -/

/-- ### 数列极限表达式常数
    ### Constant Sequence Limit Expression
    Please use tactic `lim_simp` instead -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma SeqLimitExpr.Const {L : ℝ}
  : limₙ (fun _ ↦ L) = the L
:= sorry

/-- ### 函数极限表达式常数
    ### Constant Function Limit Expression
    Please use tactic `lim_simp` instead -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma FuncLimitExpr.Const {x₀ L : ℝ}
  : lim (fun _ ↦ L) x₀ = the L
:= sorry

/-- ### 左极限表达式常数
    ### Constant Left Limit Expression
    Please use tactic `lim_simp` instead -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma LeftLimitExpr.Const {x₀ L : ℝ}
  : lim₋ (fun _ ↦ L) x₀ = the L
:= sorry

/-- ### 右极限表达式常数
    ### Constant Right Limit Expression
    Please use tactic `lim_simp` instead -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma RightLimitExpr.Const {x₀ L : ℝ}
  : lim₊ (fun _ ↦ L) x₀ = the L
:= sorry


/- ## 极限运算法则 Limit Calculation Rules -/

/-- ### 数列极限加法
    ### Sequence Limit Addition -/
theorem SeqLimit_Add {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B)
  : SeqLimit (a + b) (A + B)
:= sorry

/-- ### 数列极限加法（表达式）
    ### Sequence Limit Addition (Expression) -/
theorem SeqLimit_Add? {a b : Sequence}
  : limₙ (a + b) =? limₙ a + limₙ b
:= sorry

/-- ### 函数极限加法
    ### Function Limit Addition -/
theorem FuncLimit_Add {F G : Function} {x₀ A B : ℝ}
    (h_f : FuncLimit f x₀ A) (h_g : FuncLimit g x₀ B)
  : FuncLimit (f + g) x₀ (A + B)
:= sorry

/-- ### 函数极限加法（表达式）
    ### Function Limit Addition (Expression) -/
theorem FuncLimit_Add? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f + g) x₀ =? lim f x₀ + lim g x₀
:= sorry

/-- ### 左极限加法（表达式）
    ### Left Limit Addition (Expression) -/
theorem LeftLimit_Add? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f + g) x₀ =? lim₋ f x₀ + lim₋ g x₀
:= sorry

/-- ### 右极限加法（表达式）
    ### Right Limit Addition (Expression) -/
theorem RightLimit_Add? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f + g) x₀ =? lim₊ f x₀ + lim₊ g x₀
:= sorry

/-- ### 数列极限减法
    ### Sequence Limit Subtraction -/
theorem SeqLimit_Sub {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B)
  : SeqLimit (a - b) (A - B)
:= sorry

/-- ### 数列极限减法（表达式）
    ### Sequence Limit Subtraction (Expression) -/
theorem SeqLimit_Sub? {a b : Sequence}
  : limₙ (a - b) =? limₙ a - limₙ b
:= sorry

/-- ### 函数极限减法
    ### Function Limit Subtraction -/
theorem FuncLimit_Sub {F G : Function} {x₀ A B : ℝ}
    (h_f : FuncLimit f x₀ A) (h_g : FuncLimit g x₀ B)
  : FuncLimit (f - g) x₀ (A - B)
:= sorry

/-- ### 函数极限减法（表达式）
    ### Function Limit Subtraction (Expression) -/
theorem FuncLimit_Sub? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f - g) x₀ =? lim f x₀ - lim g x₀
:= sorry

/-- ### 左极限减法（表达式）
    ### Left Limit Subtraction (Expression) -/
theorem LeftLimit_Sub? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f - g) x₀ =? lim₋ f x₀ - lim₋ g x₀
:= sorry

/-- ### 右极限减法（表达式）
    ### Right Limit Subtraction (Expression) -/
theorem RightLimit_Sub? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f - g) x₀ =? lim₊ f x₀ - lim₊ g x₀
:= sorry

/-- ### 数列极限乘法
    ### Sequence Limit Multiplication -/
theorem SeqLimit_Mul {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B)
  : SeqLimit (a * b) (A * B)
:= sorry

/-- ### 数列极限乘法（表达式）
    ### Sequence Limit Multiplication (Expression) -/
theorem SeqLimit_Mul? {a b : Sequence}
  : limₙ (a * b) =? limₙ a * limₙ b
:= sorry

/-- ### 函数极限乘法
    ### Function Limit Multiplication -/
theorem FuncLimit_Mul {F G : Function} {x₀ A B : ℝ}
    (h_f : FuncLimit f x₀ A) (h_g : FuncLimit g x₀ B)
  : FuncLimit (f * g) x₀ (A * B)
:= sorry

/-- ### 函数极限乘法（表达式）
    ### Function Limit Multiplication (Expression) -/
theorem FuncLimit_Mul? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f * g) x₀ =? lim f x₀ * lim g x₀
:= sorry

/-- ### 左极限乘法（表达式）
    ### Left Limit Multiplication (Expression) -/
theorem LeftLimit_Mul? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f * g) x₀ =? lim₋ f x₀ * lim₋ g x₀
:= sorry

/-- ### 右极限乘法（表达式）
    ### Right Limit Multiplication (Expression) -/
theorem RightLimit_Mul? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f * g) x₀ =? lim₊ f x₀ * lim₊ g x₀
:= sorry

/-- ### 数列极限除法
    ### Sequence Limit Division -/
theorem SeqLimit_Div {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B)
  : SeqLimit (a / b) (A / B)
:= sorry

/-- ### 数列极限除法（表达式）
    ### Sequence Limit Division (Expression)
    - Note that there's no need to ensure that the denominator is non-zero here -/
theorem SeqLimit_Div? {a b : Sequence}
  : limₙ (a / b) =? limₙ a / limₙ b
:= sorry

/-- ### 函数极限除法
    ### Function Limit Division -/
theorem FuncLimit_Div {F G : Function} {x₀ A B : ℝ}
    (h_f : FuncLimit f x₀ A) (h_g : FuncLimit g x₀ B) /- 此处补充非零检查 -/
  : FuncLimit (f / g) x₀ (A / B)
:= sorry

/-- ### 函数极限除法（表达式）
    ### Function Limit Division (Expression)
    - Note that there's no need to ensure that the denominator is non-zero here -/
theorem FuncLimit_Div? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f / g) x₀ =? lim f x₀ / lim g x₀
:= sorry

/-- ### 左极限除法（表达式）
    ### Left Limit Division (Expression)
    - Note that there's no need to ensure that the denominator is non-zero here -/
theorem LeftLimit_Div? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f / g) x₀ =? lim₋ f x₀ / lim₋ g x₀
:= sorry

/-- ### 右极限除法（表达式）
    ### Right Limit Division (Expression)
    - Note that there's no need to ensure that the denominator is non-zero here -/
theorem RightLimit_Div? {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f / g) x₀ =? lim₊ f x₀ / lim₊ g x₀
:= sorry

/-- ### 函数极限复合（表达式）
    ### Function Limit Composition (Expression) -/
-- @[aesop unsafe 10% apply (rule_sets := [LimitSimplify])]
theorem FuncLimit_Comp? {x₀ gx₀ : ℝ} {f g : ℝ → ℝ} (h_gx₀ : lim₊ g x₀ = the gx₀)
  : lim₊ (fun x ↦ f (g x)) x₀ =? lim₊ f gx₀
:= sorry

/-- ### 极限 ⇒ 左极限
    ### Function Limit ⇒ Left Limit -/
theorem FuncLimit.toLeft {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : LeftLimit F x₀ L
:= sorry

/-- ### 极限 ⇒ 右极限
    ### Function Limit ⇒ Right Limit -/
theorem FuncLimit.toRight {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : RightLimit F x₀ L
:= sorry

/-- ### 极限 ⇒ 左极限（表达式）
    ### Function Limit ⇒ Left Limit (Expression) -/
theorem FuncLimitExpr.toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f x₀ =? lim f x₀
:= sorry

/-- ### 极限 ⇒ 右极限（表达式）
    ### Function Limit ⇒ Right Limit (Expression) -/
theorem FuncLimitExpr.toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f x₀ =? lim f x₀
:= sorry

/-- ### 夹逼定理（数列极限）
    ### Squeeze Theorem (Sequence Limit) -/
theorem SeqLimitSqueeze {a b c : Sequence} {L : ℝ}
    (h_a : limₙ a = the L) (h_c : limₙ c = the L)
    (h_chain : ∀ n, a n ≤ b n ∧ b n ≤ c n)
  : limₙ b = the L
:= sorry

/-- ### 夹逼定理（函数极限）
    ### Squeeze Theorem (Function Limit) -/
theorem FuncLimitSqueeze {f g h : ℝ → ℝ} {x₀ L : ℝ}
    (h_f : lim f x₀ = the L) (h_h : lim h x₀ = the L)
    (h_chain : ∀ x, f x ≤ g x ∧ g x ≤ h x)
  : lim g x₀ = the L
:= sorry
