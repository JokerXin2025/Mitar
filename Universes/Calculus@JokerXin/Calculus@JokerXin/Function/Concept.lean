import «Calculus@JokerXin».Prelude
import «Calculus@JokerXin».Function.Defs


/- # 邻域 Neighborhood -/

/-- ### 邻域
    ### Neighborhood -/
abbrev Nbho (x₀ δ : ℝ) : Set ℝ := Ioo (x₀ - δ) (x₀ + δ)

/-- ### 去心邻域
    ### Deleted Neighborhood -/
abbrev Nbhd (x₀ δ : ℝ) : Set ℝ := Ioo (x₀ - δ) x₀ ∪ Ioo x₀ (x₀ + δ)

/-- ### 去心邻域 ⊆ 邻域 -/
lemma Nbhd_subset_Nbho {x₀ δ : ℝ}
  : Nbhd x₀ δ ⊆ Nbho x₀ δ
:= sorry


/- # 最值点 Minimum Point / Maximum Point -/

/-- ### 最小值点
    ### Minimum Point -/
def isMinimumPoint (F : Function) (m : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x > F.map m

/-- ### 最大值点
    ### Maximum Point -/
def isMaximumPoint (F : Function) (M : ℝ) : Prop :=
  ∀ x ∈ F.domain, F.map x < F.map M


/- ## 函数有界性 Boundedness of Function -/

/-- ### 有界
    ### Bounded -/
def FuncBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, |F.map x| < M

/-- ### 有上界
    ### Upper-Bounded -/
def FuncUpperBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x < M

/-- ### 有下界
    ### Lower-Bounded -/
def FuncLowerBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x > -M

/-- ### 局部有界
    ### Locally Bounded -/
def FuncLocalBounded (F : Function) (x₀ δ : ℝ) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain ∩ Nbho x₀ δ, |F.map x| < M
