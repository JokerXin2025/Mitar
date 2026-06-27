import «Calculus@Mitar».Limit.Expr


/- ## 无穷小 Infinitesimal -/

/-- ### 无穷小
    ### Infinitesimal -/
@[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0)$" Text]
abbrev isInfinitesimal (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  lim f x₀ = the 0

/-- ### 左无穷小
    ### Left Infinitesimal -/
@[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0^-)$" Text]
abbrev isLeftInfinitesimal (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  lim₋ f x₀ = the 0

/-- ### 右无穷小
    ### Right Infinitesimal -/
@[Lean2TeX "@1是无穷小量 $(#1(ℝ)\\to 0^+)$" Text]
abbrev isRightInfinitesimal (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  lim₊ f x₀ = the 0

/- ## 无穷小的阶 Order of Infinitesimal -/

/-- ### 高阶无穷小
    ### Higher Order Infinitesimal -/
def isHigherInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  lim (f / g) x₀ = the 0

/-- ### 高阶左无穷小
    ### Higher Order Left Infinitesimal -/
def isHigherLeftInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  lim₋ (f / g) x₀ = the 0

/-- ### 高阶右无穷小
    ### Higher Order Right Infinitesimal -/
def isHigherRightInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  lim₊ (f / g) x₀ = the 0
