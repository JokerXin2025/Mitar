import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Infinitesimal.Defs


/- ## 高阶无穷小 Higher Order Infinitesimal -/

/-- ### 高阶无穷小
    ### Higher Order Infinitesimal -/
def isHigherInfinitesimal (F G : Function) (x₀ : ℝ) : Prop :=
  isInfinitesimal F x₀ ∧ isInfinitesimal G x₀
  ∧ FuncLimit (F / G) x₀ 0

/-- ### 高阶左无穷小
    ### Higher Order Left Infinitesimal -/
def isHigherLeftInfinitesimal (F G : Function) (x₀ : ℝ) : Prop :=
  isInfinitesimal F x₀ ∧ isInfinitesimal G x₀
  ∧ LeftLimit (F / G) x₀ 0

/-- ### 高阶右无穷小
    ### Higher Order Right Infinitesimal -/
def isHigherRightInfinitesimal (F G : Function) (x₀ : ℝ) : Prop :=
  isInfinitesimal F x₀ ∧ isInfinitesimal G x₀
  ∧ RightLimit (F / G) x₀ 0
