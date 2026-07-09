import «Calculus@JokerXin».Limit.Expr


/- ## 无穷小 Infinitesimal -/

/-- ### 无穷小
    ### Infinitesimal -/
@[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0)$" Text]
abbrev isInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  FuncLimit F x₀ 0

/-- ### 左无穷小
    ### Left Infinitesimal -/
@[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0^-)$" Text]
abbrev isLeftInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  LeftLimit F x₀ 0

/-- ### 右无穷小
    ### Right Infinitesimal -/
@[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0^+)$" Text]
abbrev isRightInfinitesimal (F : Function) (x₀ : ℝ) : Prop :=
  RightLimit F x₀ 0


/- ## 基本无穷小 Basic Infinitesimals -/

/-- ### 自然指数无穷小（表达式）
    ### Natural Exponent Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ExpInfinitesimal {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim ↑(fun x ↦ e ^ f x - 1) 0 = the 0
:= sorry

/-- ### 自然指数左无穷小（表达式）
    ### Natural Exponent Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ExpInfinitesimal_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ ↑(fun x ↦ e ^ f x - 1) 0 = the 0
:= sorry

/-- ### 自然指数右无穷小（表达式）
    ### Natural Exponent Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ExpInfinitesimal_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ ↑(fun x ↦ e ^ f x - 1) 0 = the 0
:= sorry

/-- ### 自然对数无穷小（表达式）
    ### Natural Logarithm Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma LnInfinitesimal {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (fun x ↦ ln (1 + f x)) 0 = the 0
:= sorry

/-- ### 自然对数左无穷小（表达式）
    ### Natural Logarithm Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma LnInfinitesimal_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (fun x ↦ ln (1 + f x)) 0 = the 0
:= sorry

/-- ### 自然对数右无穷小（表达式）
    ### Natural Logarithm Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma LnInfinitesimal_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (fun x ↦ ln (1 + f x)) 0 = the 0
:= sorry

/-- ### 幂无穷小（表达式）
    ### Power Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma PowInfinitesimal {a : ℝ} {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (((1 + ·)^a - 1) ∘ f : ℝ → ℝ) 0 = the 0
:= sorry

/-- ### 幂左无穷小（表达式）
    ### Power Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma PowInfinitesimal_Left {a : ℝ} {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (((1 + ·)^a - 1) ∘ f : ℝ → ℝ) 0 = the 0
:= sorry

/-- ### 幂右无穷小（表达式）
    ### Power Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma PowInfinitesimal_Right {a : ℝ} {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (((1 + ·)^a - 1) ∘ f : ℝ → ℝ) 0 = the 0
:= sorry

/-- ### 正弦无穷小（表达式）
    ### Sine Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma SinInfinitesimal {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (sin ∘ f) 0 = the 0
:= sorry

/-- ### 正弦左无穷小（表达式）
    ### Sine Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma SinInfinitesimal_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (sin ∘ f) 0 = the 0
:= sorry

/-- ### 正弦右无穷小（表达式）
    ### Sine Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma SinInfinitesimal_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (sin ∘ f) 0 = the 0
:= sorry

/-- ### 正切无穷小（表达式）
    ### Tangent Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma TanInfinitesimal {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (tan ∘ f) 0 = the 0
:= sorry

/-- ### 正切左无穷小（表达式）
    ### Tangent Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma TanInfinitesimal_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (tan ∘ f) 0 = the 0
:= sorry

/-- ### 正切右无穷小（表达式）
    ### Tangent Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma TanInfinitesimal_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (tan ∘ f) 0 = the 0
:= sorry

/-- ### 反正弦无穷小（表达式）
    ### Arc-Sine Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ArcsinInfinitesimal {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (arcsin ∘ f) 0 = the 0
:= sorry

/-- ### 反正弦左无穷小（表达式）
    ### Arc-Sine Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ArcsinInfinitesimal_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (arcsin ∘ f) 0 = the 0
:= sorry

/-- ### 反正弦右无穷小（表达式）
    ### Arc-Sine Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ArcsinInfinitesimal_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (arcsin ∘ f) 0 = the 0
:= sorry

/-- ### 反正切无穷小（表达式）
    ### Arc-Tangent Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ArctanInfinitesimal {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (arctan ∘ f) 0 = the 0
:= sorry

/-- ### 反正切左无穷小（表达式）
    ### Arc-Tangent Left Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ArctanInfinitesimal_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (arctan ∘ f) 0 = the 0
:= sorry

/-- ### 反正切右无穷小（表达式）
    ### Arc-Tangent Right Infinitesimal (Expression) -/
@[aesop norm simp (rule_sets := [LimitInfinitesimal])]
lemma ArctanInfinitesimal_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (arctan ∘ f) 0 = the 0
:= sorry
