import «Calculus@JokerXin».Function.Continuity.Rules
import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Rules


/- ## 初等函数的连续性 Elementary Functions' Continuity -/

/-- ### 常函数的连续性
    ### Constant Function's Continuity -/
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

/-- ### 常函数的连续性（表达式）
    ### Constant Function's Continuity (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Constant {C x₀ : ℝ}
  : lim (fun _ ↦ C) x₀ = the C
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Constant_isContinuous x₀ (mem_univ x₀)

/-- ### 常函数的左连续性（表达式）
    ### Constant Function's Left Continuity (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Constant {C x₀ : ℝ}
  : lim₋ (fun _ ↦ C) x₀ = the C
:= by
  calc
    lim₋ (fun _ ↦ C) x₀ =? lim (fun _ ↦ C) x₀
                           := FuncLimitExpr.toLeft
    _                   =  the C
                           := FuncLimitExpr.Constant

/-- ### 常函数的左连续性（表达式）
    ### Constant Function's Left Continuity (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Constant {C x₀ : ℝ}
  : lim₊ (fun _ ↦ C) x₀ = the C
:= by
  calc
    lim₊ (fun _ ↦ C) x₀ =? lim (fun _ ↦ C) x₀
                           := FuncLimitExpr.toRight
    _                   =  the C
                           := FuncLimitExpr.Constant

/-- ### 恒等函数的连续性
    ### Identity Function's Continuity -/
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

/-- ### 恒等函数的连续性（表达式）
    ### Identity Function's Continuity (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Identity {x₀ : ℝ}
  : lim (·) x₀ = the x₀
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Identity_isContinuous x₀ (mem_univ x₀)

/-- ### 恒等函数的左连续性（表达式）
    ### Identity Function's Left Continuity (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Identity {x₀ : ℝ}
  : lim₋ (·) x₀ = the x₀
:= by
  calc
    lim₋ (·) x₀ =? lim (·) x₀
                   := FuncLimitExpr.toLeft
    _           =  the x₀
                   := FuncLimitExpr.Identity

/-- ### 恒等函数的右连续性（表达式）
    ### Identity Function's Right Continuity (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Identity {x₀ : ℝ}
  : lim₊ (·) x₀ = the x₀
:= by
  calc
    lim₊ (·) x₀ =? lim (·) x₀
                   := FuncLimitExpr.toRight
    _           =  the x₀
                   := FuncLimitExpr.Identity

/-- ### 绝对值函数的连续性
    ### Absolute Value Function's Continuity -/
lemma Abs_isContinuous
  : isContinuous Abs
:= sorry

/-- ### 绝对值函数的连续性（表达式）
    ### Absolute Value Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Abs {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim ↑((|·|) ∘ f) x₀ = the |u₀|
:= FuncLimitExpr.CompSV h_u₀ sorry

/-- ### 绝对值函数的左连续性（表达式）
    ### Absolute Value Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Abs {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑((|·|) ∘ f) x₀ = the |u₀|
:= by
  calc
    lim₋ ↑((|·|) ∘ f) x₀ =? lim ↑((|·|) ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the |u₀|
                   := FuncLimitExpr.Abs h_u₀

/-- ### 绝对值函数的右连续性（表达式）
    ### Absolute Value Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Abs {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑((|·|) ∘ f) x₀ = the |u₀|
:= by
  calc
    lim₊ ↑((|·|) ∘ f) x₀ =? lim ↑((|·|) ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the |u₀|
                   := FuncLimitExpr.Abs h_u₀

/- # To be Modified ↓ -/
/-
/-- ### 幂函数的内部连续性
    ### Power Function's Internal Continuity -/
lemma Power.isContinuous {a : ℕ}
  : ∀ x > 0, isContinuousAt (Power a) x
:= sorry

/-- ### 幂函数在0处的右连续性
    ### Power Function's Right Continuity at `0`
    - If `Power a`'s domain doesn't cover `Iii`, this version may be useful. -/
lemma Power.isContinuous_0Right {a : ℕ}
  : isRightContinuousAt (Power a) 0
:= sorry

/-- ### 幂函数的连续性（表达式）
    ### Power Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Power {a x₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
    (h_inter : x₀ > 0)
  : lim (·^a) x₀ = the (x₀^a)
:= by
  apply FuncLimit_to_FuncLimitExpr
  exact Power.isContinuous x₀ (mem_univ x₀)

/-- ### 幂函数的左连续性（表达式）
    ### Power Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Power {a x₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (·^a) x₀ = the (x₀^a)
:= by
  calc
    lim₋ (·^a) x₀ =? lim (·^a) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (x₀^a)
                   := FuncLimitExpr.Power

/-- ### 幂函数的右连续性（表达式）
    ### Power Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Power {a x₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (·^a) x₀ = the (x₀^a)
:= by
  calc
    lim₊ (·^a) x₀ =? lim (·^a) x₀
                   := FuncLimitExpr.toRight
    _           =  the (x₀^a)
                   := FuncLimitExpr.Power
-/

/-- ### 平方根函数的内部连续性
    ### Square Root Function's Internal Continuity -/
lemma Sqrt_isContinuous
  : ∀ x > 0, isContinuousAt Sqrt x
:= sorry

/-- ### 平方根函数在0处的右连续性
    ### Square Root Function's Right Continuity at `0` -/
lemma Sqrt_isContinuous_0Right
  : isRightContinuousAt Sqrt 0
:= sorry

/-- ### 平方根函数的连续性（表达式）
    ### Square Root Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sqrt {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim ((√·) ∘ f) x₀ = the (√u₀)
:= sorry

/-- ### 平方根函数的左连续性（表达式）
    ### Square Root Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sqrt {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ((√·) ∘ f) x₀ = the (√u₀)
:= by
  calc
    lim₋ ((√·) ∘ f) x₀ =? lim ((√·) ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (√u₀)
                   := FuncLimitExpr.Sqrt h_dom h_u₀

/-- ### 平方根函数的右连续性（表达式）
    ### Square Root Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sqrt {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≥ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ((√·) ∘ f) x₀ = the (√u₀)
:= sorry

/-- ### 自然指数函数的连续性
    ### Natural Exponential Function's Continuity -/
lemma Exp_isContinuous
  : isContinuous Exp
:= sorry

/-- ### 自然指数函数的连续性（表达式）
    ### Natural Exponential Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Exp {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (exp ∘ f) x₀ = the (exp u₀)
:= sorry

/-- ### 自然指数函数的左连续性（表达式）
    ### Natural Exponential Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Exp {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(exp ∘ f) x₀ = the (exp u₀)
:= by
  calc
    lim₋ ↑(exp ∘ f) x₀ =? lim (exp ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (exp u₀)
                   := FuncLimitExpr.Exp h_u₀

/-- ### 自然指数函数的右连续性（表达式）
    ### Natural Exponential Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Exp {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(exp ∘ f) x₀ = the (exp u₀)
:= by
  calc
    lim₊ ↑(exp ∘ f) x₀ =? lim (exp ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (exp u₀)
                   := FuncLimitExpr.Exp h_u₀

/-- ### 自然对数函数的连续性
    ### Natural Logarithm Function's Continuity -/
lemma Ln_isContinuous
  : isContinuous Ln
:= sorry

/-- ### 自然对数函数的连续性（表达式）
    ### Natural Logarithm Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Ln {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (ln ∘ f) x₀ = the (ln u₀)
:= sorry

/-- ### 自然对数函数的左连续性（表达式）
    ### Natural Logarithm Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Ln {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(ln ∘ f) x₀ = the (ln u₀)
:= by
  calc
    lim₋ ↑(ln ∘ f) x₀ =? lim (ln ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (ln u₀)
                   := FuncLimitExpr.Ln h_dom h_u₀

/-- ### 自然对数函数的右连续性（表达式）
    ### Natural Logarithm Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Ln {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(ln ∘ f) x₀ = the (ln u₀)
:= by
  calc
    lim₊ ↑(ln ∘ f) x₀ =? lim (ln ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (ln u₀)
                   := FuncLimitExpr.Ln h_dom h_u₀

/-- ### 正弦函数的连续性
    ### Sine Function's Continuity -/
lemma Sin_isContinuous
  : isContinuous Sin
:= sorry

/-- ### 正弦函数的连续性（表达式）
    ### Sine Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sin {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (sin ∘ f) x₀ = the (sin u₀)
:= sorry

/-- ### 正弦函数的左连续性（表达式）
    ### Sine Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sin {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(sin ∘ f) x₀ = the (sin u₀)
:= by
  calc
    lim₋ ↑(sin ∘ f) x₀ =? lim (sin ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (sin u₀)
                   := FuncLimitExpr.Sin h_u₀

/-- ### 正弦函数的右连续性（表达式）
    ### Sine Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sin {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(sin ∘ f) x₀ = the (sin u₀)
:= by
  calc
    lim₊ ↑(sin ∘ f) x₀ =? lim (sin ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (sin u₀)
                   := FuncLimitExpr.Sin h_u₀

/-- ### 余弦函数的连续性
    ### Cosine Function's Continuity -/
lemma Cos_isContinuous
  : isContinuous Cos
:= sorry

/-- ### 余弦函数的连续性（表达式）
    ### Cosine Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Cos {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (cos ∘ f) x₀ = the (cos u₀)
:= sorry

/-- ### 余弦函数的左连续性（表达式）
    ### Cosine Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Cos {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(cos ∘ f) x₀ = the (cos u₀)
:= by
  calc
    lim₋ ↑(cos ∘ f) x₀ =? lim (cos ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (cos u₀)
                   := FuncLimitExpr.Cos h_u₀

/-- ### 余弦函数的右连续性（表达式）
    ### Cosine Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Cos {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(cos ∘ f) x₀ = the (cos u₀)
:= by
  calc
    lim₊ ↑(cos ∘ f) x₀ =? lim (cos ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (cos u₀)
                   := FuncLimitExpr.Cos h_u₀

/-- ### 正切函数的连续性
    ### Tangent Function's Continuity -/
lemma Tan_isContinuous
  : isContinuous Tan
:= sorry

/-- ### 正切函数的连续性（表达式）
    ### Tangent Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Tan {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (tan ∘ f) x₀ = the (sin u₀) / the (cos u₀)
:= sorry

/-- ### 正切函数的左连续性（表达式）
    ### Tangent Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Tan {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (tan ∘ f) x₀ = the (sin u₀) / the (cos u₀)
:= sorry

/-- ### 正切函数的右连续性（表达式）
    ### Tangent Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Tan {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (tan ∘ f) x₀ = the (sin u₀) / the (cos u₀)
:= sorry

/-- ### 余切函数的连续性
    ### Cotangent Function's Continuity -/
lemma Cot_isContinuous
  : isContinuous Cot
:= sorry

/-- ### 余切函数的连续性（表达式）
    ### Cotangent Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Cot {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (cot ∘ f) x₀ = the (cos u₀) / the (sin u₀)
:= sorry

/-- ### 余切函数的左连续性（表达式）
    ### Cotangent Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Cot {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (cot ∘ f) x₀ = the (cos u₀) / the (sin u₀)
:= sorry

/-- ### 余切函数的右连续性（表达式）
    ### Cotangent Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Cot {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (cot ∘ f) x₀ = the (cos u₀) / the (sin u₀)
:= sorry

/-- ### 正割函数的连续性
    ### Secant Function's Continuity -/
lemma Sec_isContinuous
  : isContinuous Sec
:= sorry

/-- ### 正割函数的连续性（表达式）
    ### Secant Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sec {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (sec ∘ f) x₀ = the 1 / the (cos u₀)
:= sorry

/-- ### 正割函数的左连续性（表达式）
    ### Secant Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sec {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (sec ∘ f) x₀ = the 1 / the (cos u₀)
:= sorry

/-- ### 正割函数的右连续性（表达式）
    ### Secant Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sec {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (sec ∘ f) x₀ = the 1 / the (cos u₀)
:= sorry

/-- ### 余割函数的连续性
    ### Cosecant Function's Continuity -/
lemma Csc_isContinuous
  : isContinuous Csc
:= sorry

/-- ### 余割函数的连续性（表达式）
    ### Cosecant Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Csc {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (csc ∘ f) x₀ = the 1 / the (sin u₀)
:= sorry

/-- ### 余割函数的左连续性（表达式）
    ### Cosecant Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Csc {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (csc ∘ f) x₀ = the 1 / the (sin u₀)
:= sorry

/-- ### 余割函数的右连续性（表达式）
    ### Cosecant Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Csc {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (csc ∘ f) x₀ = the 1 / the (sin u₀)
:= sorry

/-- ### 双曲正弦函数的连续性
    ### Hyp-Sine Function's Continuity -/
lemma Sinh_isContinuous
  : isContinuous Sinh
:= sorry

/-- ### 双曲正弦函数的连续性（表达式）
    ### Hyp-Sine Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sinh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (sinh ∘ f) x₀ = the (sinh u₀)
:= sorry

/-- ### 双曲正弦函数的左连续性（表达式）
    ### Hyp-Sine Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sinh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(sinh ∘ f) x₀ = the (sinh u₀)
:= by
  calc
    lim₋ ↑(sinh ∘ f) x₀ =? lim (sinh ∘ f) x₀
                    := FuncLimitExpr.toLeft
    _            =  the (sinh u₀)
                    := FuncLimitExpr.Sinh h_u₀

/-- ### 双曲正弦函数的右连续性（表达式）
    ### Hyp-Sine Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sinh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(sinh ∘ f) x₀ = the (sinh u₀)
:= by
  calc
    lim₊ ↑(sinh ∘ f) x₀ =? lim (sinh ∘ f) x₀
                    := FuncLimitExpr.toRight
    _            =  the (sinh u₀)
                    := FuncLimitExpr.Sinh h_u₀

/-- ### 双曲余弦函数的连续性
    ### Hyp-Cosine Function's Continuity -/
lemma Cosh_isContinuous
  : isContinuous Cosh
:= sorry

/-- ### 双曲余弦函数的连续性（表达式）
    ### Hyp-Cosine Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Cosh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (cosh ∘ f) x₀ = the (cosh u₀)
:= sorry

/-- ### 双曲余弦函数的左连续性（表达式）
    ### Hyp-Cosine Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Cosh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(cosh ∘ f) x₀ = the (cosh u₀)
:= by
  calc
    lim₋ ↑(cosh ∘ f) x₀ =? lim (cosh ∘ f) x₀
                    := FuncLimitExpr.toLeft
    _            =  the (cosh u₀)
                    := FuncLimitExpr.Cosh h_u₀

/-- ### 双曲余弦函数的右连续性（表达式）
    ### Hyp-Cosine Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Cosh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(cosh ∘ f) x₀ = the (cosh u₀)
:= by
  calc
    lim₊ ↑(cosh ∘ f) x₀ =? lim (cosh ∘ f) x₀
                    := FuncLimitExpr.toRight
    _            =  the (cosh u₀)
                    := FuncLimitExpr.Cosh h_u₀

/-- ### 双曲正切函数的连续性
    ### Hyp-Tangent Function's Continuity -/
lemma Tanh_isContinuous
  : isContinuous Tanh
:= sorry

/-- ### 双曲正切函数的连续性（表达式）
    ### Hyp-Tangent Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Tanh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (tanh ∘ f) x₀ = the (tanh u₀)
:= sorry

/-- ### 双曲正切函数的左连续性（表达式）
    ### Hyp-Tangent Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Tanh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(tanh ∘ f) x₀ = the (tanh u₀)
:= by
  calc
    lim₋ ↑(tanh ∘ f) x₀ =? lim (tanh ∘ f) x₀
                    := FuncLimitExpr.toLeft
    _            =  the (tanh u₀)
                    := FuncLimitExpr.Tanh h_u₀

/-- ### 双曲正切函数的右连续性（表达式）
    ### Hyp-Tangent Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Tanh {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(tanh ∘ f) x₀ = the (tanh u₀)
:= by
  calc
    lim₊ ↑(tanh ∘ f) x₀ =? lim (tanh ∘ f) x₀
                    := FuncLimitExpr.toRight
    _            =  the (tanh u₀)
                    := FuncLimitExpr.Tanh h_u₀

/-- ### 双曲余切函数的连续性
    ### Hyp-Cotangent Function's Continuity -/
lemma Coth_isContinuous
  : isContinuous Coth
:= sorry

/-- ### 双曲余切函数的连续性（表达式）
    ### Hyp-Cotangent Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Coth {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≠ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (coth ∘ f) x₀ = the (coth u₀)
:= sorry

/-- ### 双曲余切函数的左连续性（表达式）
    ### Hyp-Cotangent Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Coth {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≠ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (coth ∘ f) x₀ = the (coth u₀)
:= sorry

/-- ### 双曲余切函数的右连续性（表达式）
    ### Hyp-Cotangent Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Coth {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≠ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (coth ∘ f) x₀ = the (coth u₀)
:= sorry

/-- ### 双曲正割函数的连续性
    ### Hyp-Secant Function's Continuity -/
lemma Sech_isContinuous
  : isContinuous Sech
:= sorry

/-- ### 双曲正割函数的连续性（表达式）
    ### Hyp-Secant Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Sech {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (sech ∘ f) x₀ = the (sech u₀)
:= sorry

/-- ### 双曲正割函数的左连续性（表达式）
    ### Hyp-Secant Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Sech {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(sech ∘ f) x₀ = the (sech u₀)
:= by
  calc
    lim₋ ↑(sech ∘ f) x₀ =? lim (sech ∘ f) x₀
                           := FuncLimitExpr.toLeft
    _                   =  the (sech u₀)
                           := FuncLimitExpr.Sech h_u₀

/-- ### 双曲正割函数的右连续性（表达式）
    ### Hyp-Secant Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Sech {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(sech ∘ f) x₀ = the (sech u₀)
:= by
  calc
    lim₊ ↑(sech ∘ f) x₀ =? lim (sech ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (sech u₀)
                   := FuncLimitExpr.Sech h_u₀

/-- ### 双曲余割函数的连续性
    ### Hyp-Cosecant Function's Continuity -/
lemma Csch_isContinuous
  : isContinuous Csch
:= sorry

/-- ### 双曲余割函数的连续性（表达式）
    ### Hyp-Cosecant Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Csch {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≠ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (csch ∘ f) x₀ = the (csch u₀)
:= sorry

/-- ### 双曲余割函数的左连续性（表达式）
    ### Hyp-Cosecant Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Csch {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≠ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (csch ∘ f) x₀ = the (csch u₀)
:= sorry

/-- ### 双曲余割函数的右连续性（表达式）
    ### Hyp-Cosecant Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Csch {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≠ 0)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (csch ∘ f) x₀ = the (csch u₀)
:= sorry

/-- ### 反正弦函数的内部连续性
    ### Arc-Sine Function's Internal Continuity -/
lemma Arcsin_isContinuous
  : ∀ x ∈ Ioo (-1) 1, isContinuousAt Arcsin x
:= sorry

/-- ### 反正弦函数在-1处的右连续性
    ### Arc-Sine Function's Right Continuity at `-1` -/
lemma Arcsin_isContinuous_neg1right
  : isRightContinuousAt Arcsin (-1)
:= sorry

/-- ### 反正弦函数在1处的左连续性
    ### Arc-Sine Function's Left Continuity at `1` -/
lemma Arcsin_isContinuous_1left
  : isLeftContinuousAt Arcsin 1
:= sorry

/-- ### 反正弦函数的连续性（表达式）
    ### Arc-Sine Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Arcsin {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (arcsin ∘ f) x₀ = the (arcsin u₀)
:= sorry

/-- ### 反正弦函数的左连续性（表达式）
    ### Arc-Sine Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Arcsin {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ ≤ 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (arcsin ∘ f) x₀ = the (arcsin u₀)
:= sorry

/-- ### 反正弦函数的右连续性（表达式）
    ### Arc-Sine Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Arcsin {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≥ -1 ∧ x₀ < 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (arcsin ∘ f) x₀ = the (arcsin u₀)
:= sorry

/-- ### 反余弦函数的内部连续性
    ### Arc-Cosine Function's Internal Continuity -/
lemma Arccos_isContinuous
  : ∀ x ∈ Ioo (-1) 1, isContinuousAt Arccos x
:= sorry

/-- ### 反余弦函数在-1处的右连续性
    ### Arc-Cosine Function's Right Continuity at `-1` -/
lemma Arccos_isContinuous_neg1right
  : isRightContinuousAt Arccos (-1)
:= sorry

/-- ### 反余弦函数在1处的左连续性
    ### Arc-Cosine Function's Left Continuity at `1` -/
lemma Arccos_isContinuous_1left
  : isLeftContinuousAt Arccos 1
:= sorry

/-- ### 反余弦函数的连续性（表达式）
    ### Arc-Cosine Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Arccos {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ < 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (arccos ∘ f) x₀ = the (arccos u₀)
:= sorry

/-- ### 反余弦函数的左连续性（表达式）
    ### Arc-Cosine Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Arccos {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ > -1 ∧ x₀ ≤ 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (arccos ∘ f) x₀ = the (arccos u₀)
:= sorry

/-- ### 反余弦函数的右连续性（表达式）
    ### Arc-Cosine Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Arccos {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≥ -1 ∧ x₀ < 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (arccos ∘ f) x₀ = the (arccos u₀)
:= sorry

/-- ### 反正切函数的连续性
    ### Arc-Tangent Function's Continuity -/
lemma Arctan_isContinuous
  : isContinuous Arctan
:= sorry

/-- ### 反正切函数的连续性（表达式）
    ### Arc-Tangent Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Arctan {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (arctan ∘ f) x₀ = the (arctan u₀)
:= sorry

/-- ### 反正切函数的左连续性（表达式）
    ### Arc-Tangent Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Arctan {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(arctan ∘ f) x₀ = the (arctan u₀)
:= by
  calc
    lim₋ ↑(arctan ∘ f) x₀ =? lim (arctan ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (arctan u₀)
                   := FuncLimitExpr.Arctan h_u₀

/-- ### 反正切函数的右连续性（表达式）
    ### Arc-Tangent Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Arctan {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(arctan ∘ f) x₀ = the (arctan u₀)
:= by
  calc
    lim₊ ↑(arctan ∘ f) x₀ =? lim (arctan ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (arctan u₀)
                   := FuncLimitExpr.Arctan h_u₀

/-- ### 反余切函数的连续性
    ### Arc-Cotangent Function's Continuity -/
lemma Arccot_isContinuous
  : isContinuous Arccot
:= sorry

/-- ### 反余切函数的连续性（表达式）
    ### Arc-Cotangent Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Arccot {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim (arccot ∘ f) x₀ = the (arccot u₀)
:= sorry

/-- ### 反余切函数的左连续性（表达式）
    ### Arc-Cotangent Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Arccot {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ ↑(arccot ∘ f) x₀ = the (arccot u₀)
:= by
  calc
    lim₋ ↑(arccot ∘ f) x₀ =? lim (arccot ∘ f) x₀
                   := FuncLimitExpr.toLeft
    _           =  the (arccot u₀)
                   := FuncLimitExpr.Arccot h_u₀

/-- ### 反余切函数的右连续性（表达式）
    ### Arc-Cotangent Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Arccot {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ ↑(arccot ∘ f) x₀ = the (arccot u₀)
:= by
  calc
    lim₊ ↑(arccot ∘ f) x₀ =? lim (arccot ∘ f) x₀
                   := FuncLimitExpr.toRight
    _           =  the (arccot u₀)
                   := FuncLimitExpr.Arccot h_u₀

/-- ### 反正割函数的内部连续性
    ### Arc-Secant Function's Internal Continuity -/
lemma Arcsec_isContinuous
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, isContinuousAt Arcsec x
:= sorry

/-- ### 反正割函数在-1处的左连续性
    ### Arc-Secant Function's Left Continuity at `-1` -/
lemma Arcsec_isContinuous_neg1left
  : isLeftContinuousAt Arcsec (-1)
:= sorry

/-- ### 反正割函数在1处的右连续性
    ### Arc-Secant Function's Right Continuity at `1` -/
lemma Arcsec_isContinuous_1right
  : isRightContinuousAt Arcsec 1
:= sorry

/-- ### 反正割函数的连续性（表达式）
    ### Arc-Secant Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Arcsec {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (arcsec ∘ f) x₀ = the (arcsec u₀)
:= sorry

/-- ### 反正割函数的左连续性（表达式）
    ### Arc-Secant Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Arcsec {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≤ -1 ∨ x₀ > 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (arcsec ∘ f) x₀ = the (arcsec u₀)
:= sorry

/-- ### 反正割函数的右连续性（表达式）
    ### Arc-Secant Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Arcsec {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ ≥ 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (arcsec ∘ f) x₀ = the (arcsec u₀)
:= sorry

/-- ### 反余割函数的内部连续性
    ### Arc-Cosecant Function's Internal Continuity -/
lemma Arccsc_isContinuous
  : ∀ x ∈ Iio (-1) ∪ Ioi 1, isContinuousAt Arccsc x
:= sorry

/-- ### 反余割函数在-1处的左连续性
    ### Arc-Cosecant Function's Left Continuity at `-1` -/
lemma Arccsc_isContinuous_neg1left
  : isLeftContinuousAt Arccsc (-1)
:= sorry

/-- ### 反余割函数在1处的右连续性
    ### Arc-Cosecant Function's Right Continuity at `1` -/
lemma Arccsc_isContinuous_1right
  : isRightContinuousAt Arccsc 1
:= sorry

/-- ### 反余割函数的连续性（表达式）
    ### Arc-Cosecant Function's Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Arccsc {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ > 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim (arccsc ∘ f) x₀ = the (arccsc u₀)
:= sorry

/-- ### 反余割函数的左连续性（表达式）
    ### Arc-Cosecant Function's Left Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Arccsc {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ ≤ -1 ∨ x₀ > 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₋ (arccsc ∘ f) x₀ = the (arccsc u₀)
:= sorry

/-- ### 反余割函数的右连续性（表达式）
    ### Arc-Cosecant Function's Right Continuity (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Arccsc {f : ℝ → ℝ} {x₀ u₀ : ℝ}
    (h_dom : x₀ < -1 ∨ x₀ ≥ 1)
    (h_u₀ : lim f x₀ = the u₀)
  : lim₊ (arccsc ∘ f) x₀ = the (arccsc u₀)
:= sorry
