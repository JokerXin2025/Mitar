import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Infinitesimal.Defs


/- ## 高阶无穷小 Higher Order Infinitesimal -/

/-- ### 高阶无穷小
    ### Higher Order Infinitesimal -/
def isHigherInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  isInfinitesimal f x₀ ∧ isInfinitesimal g x₀
  ∧ lim (f / g) x₀ = the 0

/-- ### 高阶左无穷小
    ### Higher Order Left Infinitesimal -/
def isHigherLeftInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  isInfinitesimal f x₀ ∧ isInfinitesimal g x₀
  ∧ lim₋ (f / g) x₀ = the 0

/-- ### 高阶右无穷小
    ### Higher Order Right Infinitesimal -/
def isHigherRightInfinitesimal (f g : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  isInfinitesimal f x₀ ∧ isInfinitesimal g x₀
  ∧ lim₊ (f / g) x₀ = the 0
