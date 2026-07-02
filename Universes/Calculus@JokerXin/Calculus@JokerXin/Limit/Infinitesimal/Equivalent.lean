import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Infinitesimal.Defs


/- ## 等价无穷小 Equivalent Infinitesimal -/

/-- ### 等价无穷小 Equivalent Infinitesimal -/
abbrev EquivInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (isInfinitesimal f x₀) ∧ (isInfinitesimal g x₀)
  ∧ lim (f / g) x₀ = the 1

/-- ### 左等价无穷小 Equivalent Left Infinitesimal -/
abbrev EquivLeftInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (isLeftInfinitesimal f x₀) ∧ (isLeftInfinitesimal g x₀)
  ∧ lim₋ (f / g) x₀ = the 1

/-- ### 右等价无穷小 Equivalent Right Infinitesimal -/
abbrev EquivRightInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (isRightInfinitesimal f x₀) ∧ (isRightInfinitesimal g x₀)
  ∧ lim₊ (f / g) x₀ = the 1

infix:50 " ~ " => (EquivInfinitesimal · · 0)
infix:50 " ~₋ " => (EquivLeftInfinitesimal · · 0)
infix:50 " ~₊ " => (EquivRightInfinitesimal · · 0)


/- # 基本等价无穷小 Basic Equivalent Infinitesimals -/

/-- ### 正弦的等价无穷小 Sine's Equivalent Infinitesimal -/
lemma SinEquiv {f : ℝ → ℝ} (h_ifs : isInfinitesimal f 0)
  : sin ∘ f ~ f
:= sorry

/-- ### 正弦的等价左无穷小 Sine's Equivalent Left Infinitesimal -/
lemma SinEquiv_Left {f : ℝ → ℝ} (h_ifs : isLeftInfinitesimal f 0)
  : sin ∘ f ~₋ f
:= sorry

/-- ### 正弦的等价右无穷小 Sine's Equivalent Right Infinitesimal -/
lemma SinEquiv_Right {f : ℝ → ℝ} (h_ifs : isRightInfinitesimal f 0)
  : sin ∘ f ~₊ f
:= sorry

/-- ### 正切的等价无穷小 Sine's Equivalent Infinitesimal -/
lemma TanEquiv {f : ℝ → ℝ} (h_ifs : isInfinitesimal f 0)
  : tan ∘ f ~ f
:= sorry

/-- ### 正切的等价左无穷小 Sine's Equivalent Left Infinitesimal -/
lemma TanEquiv_Left {f : ℝ → ℝ} (h_ifs : isLeftInfinitesimal f 0)
  : tan ∘ f ~₋ f
:= sorry

/-- ### 正切的等价右无穷小 Sine's Equivalent Right Infinitesimal -/
lemma TanEquiv_Right {f : ℝ → ℝ} (h_ifs : isRightInfinitesimal f 0)
  : tan ∘ f ~₊ f
:= sorry

/-- ### 自然指数的等价无穷小 Natural Exponent's Equivalent Infinitesimal -/
lemma ExpEquiv {f : ℝ → ℝ} (h_ifs : isInfinitesimal f 0)
  : (fun x ↦ e ^ x - 1) ∘ f ~ f
:= sorry

/-- ### 自然指数的等价左无穷小 Natural Exponent's Equivalent Left Infinitesimal -/
lemma ExpEquiv_Left {f : ℝ → ℝ} (h_ifs : isLeftInfinitesimal f 0)
  : (fun x ↦ e ^ x - 1) ∘ f ~₋ f
:= sorry

/-- ### 自然指数的等价右无穷小 Natural Exponent's Equivalent Right Infinitesimal -/
lemma ExpEquiv_Right {f : ℝ → ℝ} (h_ifs : isRightInfinitesimal f 0)
  : (fun x ↦ e ^ x - 1) ∘ f ~₊ f
:= sorry

/-- ### 幂的等价无穷小 Power's Equivalent Infinitesimal -/
lemma PowEquiv {a : ℝ} {f : ℝ → ℝ} (h_ifs : isInfinitesimal f 0)
  : (fun x ↦ (1 + x)^a - 1) ∘ f ~ (fun x ↦ a * x)
:= sorry

/-- ### 幂的等价左无穷小 Power's Equivalent Left Infinitesimal -/
lemma PowEquiv_Left {a : ℝ} {f : ℝ → ℝ} (h_ifs : isLeftInfinitesimal f 0)
  : (fun x ↦ (1 + x)^a - 1) ∘ f ~₋ (fun x ↦ a * f x)
:= sorry

/-- ### 幂的等价右无穷小 Power's Equivalent Right Infinitesimal -/
lemma PowEquiv_Right {a : ℝ} {f : ℝ → ℝ} (h_ifs : isRightInfinitesimal f 0)
  : (fun x ↦ (1 + x)^a - 1) ∘ f ~₊ (fun x ↦ a * f x)
:= sorry


/- ## 等价无穷小代换法则 The Rule of Equivalent Infinitesimal Substitution -/

/-- ### 分子代换 Numerator Substitution -/
theorem EquivSubst {f f' g : ℝ → ℝ} (h_equiv : f ~ f')
  : lim (fun x ↦ f x * g x) 0 =? lim (fun x ↦ f' x * g x) 0
:= sorry

/-- ### 分子代换(左极限) Numerator Substitution (Left Limit) -/
theorem EquivSubst_Left {f f' g : ℝ → ℝ} (h_equiv : f ~₋ f')
  : lim₋ (fun x ↦ f x * g x) 0 =? lim₋ (fun x ↦ f' x * g x) 0
:= sorry

/-- ### 分子代换(右极限) Numerator Substitution (Right Limit) -/
theorem EquivSubst_Right {f f' g : ℝ → ℝ} (h_equiv : f ~₊ f')
  : lim₊ (fun x ↦ f x * g x) 0 =? lim₊ (fun x ↦ f' x * g x) 0
:= sorry

/-- ### 分母代换 Denominator Substitution -/
theorem EquivSubst' {f g g' : ℝ → ℝ} (h_equiv : g ~ g')
  : lim (fun x ↦ f x / g x) 0 =? lim (fun x ↦ f x / g' x) 0
:= sorry

/-- ### 分母代换(左极限) Denominator Substitution (Left Limit) -/
theorem EquivSubst_Left' {f g g' : ℝ → ℝ} (h_equiv : g ~₋ g')
  : lim₋ (fun x ↦ f x / g x) 0 =? lim₋ (fun x ↦ f x / g' x) 0
:= sorry

/-- ### 分母代换(右极限) Denominator Substitution (Right Limit) -/
theorem EquivSubst_Right' {f g g' : ℝ → ℝ} (h_equiv : g ~₊ g')
  : lim₊ (fun x ↦ f x / g x) 0 =? lim₊ (fun x ↦ f x / g' x) 0
:= sorry
