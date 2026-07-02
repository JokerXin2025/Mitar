import «Calculus@JokerXin».Function.Defs
import «Calculus@JokerXin».Function.Continuity.Defs
import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Rules


/- ## 初等函数的连续性 Elementary Functions' Continuity -/

/-- ### 常函数的连续性
    ### Constant Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Constant_isContinuous {C : ℝ}
  : isContinuous (Constant C)
:= by
  intro _ _
  unfold isContinuousAt FuncLimit
  constructor
  · exact ⟨1, by norm_num, subset_univ _⟩
  · intro ε _
    use 1
    constructor
    · norm_num
    · intro _ _
      change C ∈ Nbho C ε
      constructor <;> linarith

/-- ### 常函数的连续性（函数极限表达式）
    ### Constant Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Constant {L x₀ : ℝ}
  : lim (fun _ ↦ L) x₀ = the L
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Constant_isContinuous x₀ (by trivial)

/-- ### 常函数的连续性（左极限表达式）
    ### Constant Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Constant {L x₀ : ℝ}
  : lim₋ (fun _ ↦ L) x₀ = the L
:= by
  calc
    lim₋ (fun _ ↦ L) x₀ =? lim (fun _ ↦ L) x₀
                           := FuncLimitExpr.toLeft
    _                   =  the L
                           := FuncLimitExpr.Constant

/-- ### 常函数的连续性（右极限表达式）
    ### Constant Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Constant {L x₀ : ℝ}
  : lim₊ (fun _ ↦ L) x₀ = the L
:= by
  calc
    lim₊ (fun _ ↦ L) x₀ =? lim (fun _ ↦ L) x₀
                           := FuncLimitExpr.toRight
    _                   =  the L
                           := FuncLimitExpr.Constant

/-- ### 恒等函数的连续性
    ### Identity Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Identity_isContinuous
  : isContinuous Identity
:= by
  intro x₀ _
  unfold isContinuousAt FuncLimit
  constructor
  · exact ⟨1, by norm_num, subset_univ _⟩
  · intro ε _
    use ε
    constructor
    · assumption
    · intro x h_x
      change x ∈ Nbho x₀ ε
      exact Nbhd_subset_Nbho h_x

/-- ### 恒等函数的连续性（函数极限表达式）
    ### Identity Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Identity {x₀ : ℝ}
  : lim (·) x₀ = the x₀
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Identity_isContinuous x₀ (by trivial)

/-- ### 恒等函数的连续性（左极限表达式）
    ### Identity Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Identity {x₀ : ℝ}
  : lim₋ (·) x₀ = the x₀
:= by
  calc
    lim₋ (·) x₀ =? lim (·) x₀
                   := FuncLimitExpr.toLeft
    _           =  the x₀
                   := FuncLimitExpr.Identity

/-- ### 恒等函数的连续性（右极限表达式）
    ### Identity Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Identity {x₀ : ℝ}
  : lim₊ (·) x₀ = the x₀
:= by
  calc
    lim₊ (·) x₀ =? lim (·) x₀
                   := FuncLimitExpr.toRight
    _           =  the x₀
                   := FuncLimitExpr.Identity

/-- ### 幂函数的连续性
    ### Power Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Power_isContinuous {a : ℕ}
  : isContinuous (Power a)
:= sorry

/-- ### 绝对值函数的连续性
    ### Absolute Value Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Abs_isContinuous
  : isContinuous Abs
:= sorry

/-- ### 绝对值函数的连续性（函数极限表达式）
    ### Absolute Value Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Abs {x₀ : ℝ}
  : lim abs x₀ = the (abs x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Abs_isContinuous x₀ (by trivial)

/-- ### 绝对值函数的连续性（左极限表达式）
    ### Absolute Value Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Abs {x₀ : ℝ}
  : lim₋ abs x₀ = the (abs x₀)
:= by
  calc
    lim₋ abs x₀ =? lim abs x₀
                   := FuncLimitExpr.toLeft
    _           =  the (abs x₀)
                   := FuncLimitExpr.Abs

/-- ### 绝对值函数的连续性（右极限表达式）
    ### Absolute Value Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Abs {x₀ : ℝ}
  : lim₊ abs x₀ = the (abs x₀)
:= by
  calc
    lim₊ abs x₀ =? lim abs x₀
                   := FuncLimitExpr.toRight
    _           =  the (abs x₀)
                   := FuncLimitExpr.Abs

/-- ### 自然指数函数的连续性
    ### Natural Exponential Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Exp_isContinuous
  : isContinuous Exp
:= sorry

/-- ### 自然指数函数的连续性（函数极限表达式）
    ### Natural Exponential Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Exp {x₀ : ℝ}
  : lim exp x₀ = the (exp x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Exp_isContinuous x₀ (by trivial)

/-- ### 自然指数函数的连续性（左极限表达式）
    ### Natural Exponential Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Exp {x₀ : ℝ}
  : lim₋ exp x₀ = the (exp x₀)
:= by
  calc
    lim₋ exp x₀ =? lim exp x₀
                   := FuncLimitExpr.toLeft
    _           =  the (exp x₀)
                   := FuncLimitExpr.Exp

/-- ### 自然指数函数的连续性（右极限表达式）
    ### Natural Exponential Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Exp {x₀ : ℝ}
  : lim₊ exp x₀ = the (exp x₀)
:= by
  calc
    lim₊ exp x₀ =? lim exp x₀
                   := FuncLimitExpr.toRight
    _           =  the (exp x₀)
                   := FuncLimitExpr.Exp

/-- ### 自然对数函数的连续性
    ### Natural Logarithm Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Ln_isContinuous
  : isContinuous Ln
:= sorry

/-- ### 自然对数函数的连续性（函数极限表达式）
    ### Natural Logarithm Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim log x₀ = the (log x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Ln_isContinuous x₀ (by trivial)

/-- ### 自然对数函数的连续性（左极限表达式）
    ### Natural Logarithm Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim₋ log x₀ = the (log x₀)
:= by
  calc
    lim₋ log x₀ =? lim log x₀
                   := FuncLimitExpr.toLeft
    _           =  the (log x₀)
                   := FuncLimitExpr.Ln h_dom

/-- ### 自然对数函数的连续性（右极限表达式）
    ### Natural Logarithm Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Ln {x₀ : ℝ}
    (h_dom : x₀ > 0)
  : lim₊ log x₀ = the (log x₀)
:= by
  calc
    lim₊ log x₀ =? lim log x₀
                   := FuncLimitExpr.toRight
    _           =  the (log x₀)
                   := FuncLimitExpr.Ln h_dom

/-- ### 正弦函数的连续性
    ### Sine Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Sin_isContinuous
  : isContinuous Sin
:= sorry

/-- ### 正弦函数的连续性（函数极限表达式）
    ### Sine Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sin {x₀ : ℝ}
  : lim sin x₀ = the (sin x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sin_isContinuous x₀ (by trivial)

/-- ### 正弦函数的连续性（左极限表达式）
    ### Sine Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sin {x₀ : ℝ}
  : lim₋ sin x₀ = the (sin x₀)
:= by
  calc
    lim₋ sin x₀ =? lim sin x₀
                   := FuncLimitExpr.toLeft
    _           =  the (sin x₀)
                   := FuncLimitExpr.Sin

/-- ### 正弦函数的连续性（右极限表达式）
    ### Sine Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sin {x₀ : ℝ}
  : lim₊ sin x₀ = the (sin x₀)
:= by
  calc
    lim₊ sin x₀ =? lim sin x₀
                   := FuncLimitExpr.toRight
    _           =  the (sin x₀)
                   := FuncLimitExpr.Sin

/-- ### 余弦函数的连续性
    ### Cosine Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Cos_isContinuous
  : isContinuous Cos
:= sorry

/-- ### 余弦函数的连续性（函数极限表达式）
    ### Cosine Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Cos {x₀ : ℝ}
  : lim cos x₀ = the (cos x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Cos_isContinuous x₀ (by trivial)

/-- ### 余弦函数的连续性（左极限表达式）
    ### Cosine Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Cos {x₀ : ℝ}
  : lim₋ cos x₀ = the (cos x₀)
:= by
  calc
    lim₋ cos x₀ =? lim cos x₀
                   := FuncLimitExpr.toLeft
    _           =  the (cos x₀)
                   := FuncLimitExpr.Cos

/-- ### 余弦函数的连续性（右极限表达式）
    ### Cosine Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Cos {x₀ : ℝ}
  : lim₊ cos x₀ = the (cos x₀)
:= by
  calc
    lim₊ cos x₀ =? lim cos x₀
                   := FuncLimitExpr.toRight
    _           =  the (cos x₀)
                   := FuncLimitExpr.Cos

/-- ### 正切函数的连续性
    ### Tangent Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Tan_isContinuous
  : isContinuous Tan
:= sorry

/-- ### 正切函数的连续性（函数极限表达式）
    ### Tangent Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Tan {x₀ : ℝ}
    (h_dom : ¬ ∃ k : ℤ, x₀ = π / 2 + k * π)
  : lim tan x₀ = the (tan x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Tan_isContinuous x₀ h_dom

/-- ### 正切函数的连续性（左极限表达式）
    ### Tangent Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Tan {x₀ : ℝ}
    (h_dom : ¬ ∃ k : ℤ, x₀ = π / 2 + k * π)
  : lim₋ tan x₀ = the (tan x₀)
:= by
  calc
    lim₋ tan x₀ =? lim tan x₀
                   := FuncLimitExpr.toLeft
    _           =  the (tan x₀)
                   := FuncLimitExpr.Tan h_dom

/-- ### 正切函数的连续性（右极限表达式）
    ### Tangent Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Tan {x₀ : ℝ}
    (h_dom : ¬ ∃ k : ℤ, x₀ = π / 2 + k * π)
  : lim₊ tan x₀ = the (tan x₀)
:= by
  calc
    lim₊ tan x₀ =? lim tan x₀
                   := FuncLimitExpr.toRight
    _           =  the (tan x₀)
                   := FuncLimitExpr.Tan h_dom

/-- ### 余切函数的连续性
    ### Cotangent Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Cot_isContinuous
  : isContinuous Cot
:= sorry

/-- ### 余切函数的连续性（函数极限表达式）
    ### Cotangent Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Cot {x₀ : ℝ}
    (h_dom : ¬ ∃ k : ℤ, x₀ = k * π)
  : lim cot x₀ = the (cot x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Cot_isContinuous x₀ h_dom

/-- ### 余切函数的连续性（左极限表达式）
    ### Cotangent Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Cot {x₀ : ℝ}
    (h_dom : ¬ ∃ k : ℤ, x₀ = k * π)
  : lim₋ cot x₀ = the (cot x₀)
:= by
  calc
    lim₋ cot x₀ =? lim cot x₀
                   := FuncLimitExpr.toLeft
    _           =  the (cot x₀)
                   := FuncLimitExpr.Cot h_dom

/-- ### 余切函数的连续性（右极限表达式）
    ### Cotangent Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Cot {x₀ : ℝ}
    (h_dom : ¬ ∃ k : ℤ, x₀ = k * π)
  : lim₊ cot x₀ = the (cot x₀)
:= by
  calc
    lim₊ cot x₀ =? lim cot x₀
                   := FuncLimitExpr.toRight
    _           =  the (cot x₀)
                   := FuncLimitExpr.Cot h_dom

/-- ### 双曲正弦函数的连续性
    ### Hyperbolic Sine Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Sinh_isContinuous
  : isContinuous Sinh
:= sorry

/-- ### 双曲正弦函数的连续性（函数极限表达式）
    ### Hyperbolic Sine Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sinh {x₀ : ℝ}
  : lim sinh x₀ = the (sinh x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Sinh_isContinuous x₀ (by trivial)

/-- ### 双曲正弦函数的连续性（左极限表达式）
    ### Hyperbolic Sine Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sinh {x₀ : ℝ}
  : lim₋ sinh x₀ = the (sinh x₀)
:= by
  calc
    lim₋ sinh x₀ =? lim sinh x₀
                    := FuncLimitExpr.toLeft
    _            =  the (sinh x₀)
                    := FuncLimitExpr.Sinh

/-- ### 双曲正弦函数的连续性（右极限表达式）
    ### Hyperbolic Sine Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sinh {x₀ : ℝ}
  : lim₊ sinh x₀ = the (sinh x₀)
:= by
  calc
    lim₊ sinh x₀ =? lim sinh x₀
                    := FuncLimitExpr.toRight
    _            =  the (sinh x₀)
                    := FuncLimitExpr.Sinh

/-- ### 双曲余弦函数的连续性
    ### Hyperbolic Cosine Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Cosh_isContinuous
  : isContinuous Cosh
:= sorry

/-- ### 双曲余弦函数的连续性（函数极限表达式）
    ### Hyperbolic Cosine Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Cosh {x₀ : ℝ}
  : lim cosh x₀ = the (cosh x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Cosh_isContinuous x₀ (by trivial)

/-- ### 双曲余弦函数的连续性（左极限表达式）
    ### Hyperbolic Cosine Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Cosh {x₀ : ℝ}
  : lim₋ cosh x₀ = the (cosh x₀)
:= by
  calc
    lim₋ cosh x₀ =? lim cosh x₀
                    := FuncLimitExpr.toLeft
    _            =  the (cosh x₀)
                    := FuncLimitExpr.Cosh

/-- ### 双曲余弦函数的连续性（右极限表达式）
    ### Hyperbolic Cosine Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Cosh {x₀ : ℝ}
  : lim₊ cosh x₀ = the (cosh x₀)
:= by
  calc
    lim₊ cosh x₀ =? lim cosh x₀
                    := FuncLimitExpr.toRight
    _            =  the (cosh x₀)
                    := FuncLimitExpr.Cosh

/-- ### 双曲正切函数的连续性
    ### Hyperbolic Tangent Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Tanh_isContinuous
  : isContinuous Tanh
:= sorry

/-- ### 双曲正切函数的连续性（函数极限表达式）
    ### Hyperbolic Tangent Function's Continuity (Function Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Tanh {x₀ : ℝ}
  : lim tanh x₀ = the (tanh x₀)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Tanh_isContinuous x₀ (by trivial)

/-- ### 双曲正切函数的连续性（左极限表达式）
    ### Hyperbolic Tangent Function's Continuity (Left Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Tanh {x₀ : ℝ}
  : lim₋ tanh x₀ = the (tanh x₀)
:= by
  calc
    lim₋ tanh x₀ =? lim tanh x₀
                    := FuncLimitExpr.toLeft
    _            =  the (tanh x₀)
                    := FuncLimitExpr.Tanh

/-- ### 双曲正切函数的连续性（右极限表达式）
    ### Hyperbolic Sine Function's Continuity (Right Limit Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Tanh {x₀ : ℝ}
  : lim₊ tanh x₀ = the (tanh x₀)
:= by
  calc
    lim₊ tanh x₀ =? lim tanh x₀
                    := FuncLimitExpr.toRight
    _            =  the (tanh x₀)
                    := FuncLimitExpr.Tanh

/-- ### 反正弦函数的连续性
    ### Arcsine Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Arcsin_isContinuous
  : isContinuous Arcsin
:= sorry

/-- ### 反余弦函数的连续性
    ### Arccosine Function's Continuity -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
lemma Arccos_isContinuous
  : isContinuous Arccos
:= sorry

/- ## 函数连续性的性质 Properties of Function's Continuity -/

/-- ### 连续性的加法 Continuity's Addition -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
theorem Continuity.Add {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= FuncLimit.Add h_f h_g

/-- ### 连续性的减法 Continuity's Subtraction -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
theorem Continuity.Sub {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= FuncLimit.Sub h_f h_g

/-- ### 连续性的乘法 Continuity's Multiplication -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
theorem Continuity.Mul {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= FuncLimit.Mul h_f h_g

/-- ### 连续性的除法 Continuity's Division -/
@[aesop safe apply (rule_sets := [FunctionContinuity])]
theorem Continuity.Div {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= FuncLimit.Div h_f h_g h_Gx₀_ne_0
