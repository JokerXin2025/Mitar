import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Infinitesimal.Defs


/- ## 等价无穷小的定义 Definitions of Equivalent Infinitesimal -/

/-- ### 等价无穷小
    ### Equivalent Infinitesimal -/
abbrev EquivInfinitesimal (F G : Function) (x₀ : ℝ) : Prop :=
  (isInfinitesimal F x₀) ∧ (isInfinitesimal G x₀)
  ∧ FuncLimit (F / G) x₀ 1

/-- ### 左等价无穷小
    ### Equivalent Left Infinitesimal -/
abbrev EquivLeftInfinitesimal (F G : Function) (x₀ : ℝ) : Prop :=
  (isLeftInfinitesimal F x₀) ∧ (isLeftInfinitesimal G x₀)
  ∧ LeftLimit (F / G) x₀ 1

/-- ### 右等价无穷小
    ### Equivalent Right Infinitesimal -/
abbrev EquivRightInfinitesimal (F G : Function) (x₀ : ℝ) : Prop :=
  (isRightInfinitesimal F x₀) ∧ (isRightInfinitesimal G x₀)
  ∧ RightLimit (F / G) x₀ 1


/- ## 基本等价无穷小 Basic Equivalent Infinitesimals -/

/-- ### 自然指数的等价无穷小（表达式）
    ### Natural Exponent's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ExpEquiv {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim ((fun x ↦ e ^ f x - 1) / f) 0 = the 1
:= sorry

/-- ### 自然指数的等价左无穷小（表达式）
    ### Natural Exponent's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ExpEquiv_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ ((fun x ↦ e ^ f x - 1) / f) 0 = the 1
:= sorry

/-- ### 自然指数的等价右无穷小（表达式）
    ### Natural Exponent's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ExpEquiv_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ ((fun x ↦ e ^ f x - 1) / f) 0 = the 1
:= sorry

/-- ### 自然对数的等价无穷小（表达式）
    ### Natural Logarithm's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LnEquiv {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim ((fun x ↦ ln (1 + f x)) / f) 0 = the 1
:= sorry

/-- ### 自然对数的等价左无穷小（表达式）
    ### Natural Logarithm's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LnEquiv_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ ((fun x ↦ ln (1 + f x)) / f) 0 = the 1
:= sorry

/-- ### 自然对数的等价右无穷小（表达式）
    ### Natural Logarithm's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma LnEquiv_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ ((fun x ↦ ln (1 + f x)) / f) 0 = the 1
:= sorry

/-- ### 幂的等价无穷小（表达式）
    ### Power's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma PowEquiv {a : ℝ} {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (((1 + ·)^a - 1) ∘ f / (a • f) : ℝ → ℝ) 0 = the 1
:= sorry

/-- ### 幂的等价左无穷小（表达式）
    ### Power's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma PowEquiv_Left {a : ℝ} {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (((1 + ·)^a - 1) ∘ f / (a • f) : ℝ → ℝ) 0 = the 1
:= sorry

/-- ### 幂的等价右无穷小（表达式）
    ### Power's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma PowEquiv_Right {a : ℝ} {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (((1 + ·)^a - 1) ∘ f / (a • f) : ℝ → ℝ) 0 = the 1
:= sorry

/-- ### 正弦的等价无穷小（表达式）
    ### Sine's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma SinEquiv {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (sin ∘ f / f) 0 = the 1
:= sorry

/-- ### 正弦的等价左无穷小（表达式）
    ### Sine's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma SinEquiv_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (sin ∘ f / f) 0 = the 1
:= sorry

/-- ### 正弦的等价右无穷小（表达式）
    ### Sine's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma SinEquiv_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (sin ∘ f / f) 0 = the 1
:= sorry

/-- ### 正切的等价无穷小（表达式）
    ### Tangent's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma TanEquiv {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (tan ∘ f / f) 0 = the 1
:= sorry

/-- ### 正切的等价左无穷小（表达式）
    ### Tangent's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma TanEquiv_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (tan ∘ f / f) 0 = the 1
:= sorry

/-- ### 正切的等价右无穷小（表达式）
    ### Tangent's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma TanEquiv_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (tan ∘ f / f) 0 = the 1
:= sorry

/-- ### 反正弦的等价无穷小（表达式）
    ### Arc-Sine's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ArcsinEquiv {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (arcsin ∘ f / f) 0 = the 1
:= sorry

/-- ### 反正弦的等价左无穷小（表达式）
    ### Arc-Sine's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ArcsinEquiv_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (arcsin ∘ f / f) 0 = the 1
:= sorry

/-- ### 反正弦的等价右无穷小（表达式）
    ### Arc-Sine's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ArcsinEquiv_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (arcsin ∘ f / f) 0 = the 1
:= sorry

/-- ### 反正切的等价无穷小（表达式）
    ### Arc-Tangent's Equivalent Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ArctanEquiv {f : ℝ → ℝ}
    (h_ifs : lim f 0 = the 0)
  : lim (arctan ∘ f / f) 0 = the 1
:= sorry

/-- ### 反正切的等价左无穷小（表达式）
    ### Arc-Tangent's Equivalent Left Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ArctanEquiv_Left {f : ℝ → ℝ}
    (h_ifs : lim₋ f 0 = the 0)
  : lim₋ (arctan ∘ f / f) 0 = the 1
:= sorry

/-- ### 反正切的等价右无穷小（表达式）
    ### Arc-Tangent's Equivalent Right Infinitesimal (Expression) -/
@[aesop unsafe 80% apply (rule_sets := [LimitBasic])]
lemma ArctanEquiv_Right {f : ℝ → ℝ}
    (h_ifs : lim₊ f 0 = the 0)
  : lim₊ (arctan ∘ f / f) 0 = the 1
:= sorry


/- ## 等价无穷小代换法则 Rules of Equivalent Infinitesimal Substitution -/

/-- ### 分子等价代换（表达式）
    ### Numerator Equivalent Substitution (Expression) -/
theorem EquivSubst {f f' g : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim (f / f') x₀ = the 1)
  : lim (fun x ↦ f x / g x) 0 =? lim (fun x ↦ f' x / g x) 0
:= sorry

/-- ### 左极限的分子等价代换（表达式）
    ### Numerator Equivalent Substitution of Left Limit (Expression) -/
theorem EquivSubst_Left {f f' g : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₋ (f / f') x₀ = the 1)
  : lim₋ (fun x ↦ f x / g x) 0 =? lim₋ (fun x ↦ f' x / g x) 0
:= sorry

/-- ### 右极限的分子等价代换（表达式）
    ### Numerator Equivalent Substitution of Right Limit (Expression) -/
theorem EquivSubst_Right {f f' g : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₊ (f / f') x₀ = the 1)
  : lim₊ (fun x ↦ f x / g x) 0 =? lim₊ (fun x ↦ f' x / g x) 0
:= sorry

/-- ### 分母等价代换（表达式）
    ### Denominator Equivalent Substitution (Expression) -/
theorem EquivSubst' {f g g' : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim (g / g') x₀ = the 1)
  : lim (fun x ↦ f x / g x) 0 =? lim (fun x ↦ f x / g' x) 0
:= sorry

/-- ### 左极限的分母等价代换（表达式）
    ### Denominator Equivalent Substitution of Left Limit (Expression) -/
theorem EquivSubst_Left' {f g g' : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₋ (g / g') x₀ = the 1)
  : lim₋ (fun x ↦ f x / g x) 0 =? lim₋ (fun x ↦ f x / g' x) 0
:= sorry

/-- ### 右极限的分母等价代换（表达式）
    ### Denominator Equivalent Substitution of Right Limit (Expression) -/
theorem EquivSubst_Right' {f g g' : ℝ → ℝ} {x₀ : ℝ}
    (h_equiv : lim₊ (g / g') x₀ = the 1)
  : lim₊ (fun x ↦ f x / g x) 0 =? lim₊ (fun x ↦ f x / g' x) 0
:= sorry
