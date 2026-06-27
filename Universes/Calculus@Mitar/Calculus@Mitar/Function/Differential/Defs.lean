import «Calculus@Mitar».Limit.Defs
import «Calculus@Mitar».Function.Continuous.Defs


/- ## 导数的定义 Definitions of Derivative -/

/-- ### 导数
    ### Derivative -/
def Deriv (F : Function) (x₀ L : ℝ) : Prop :=
  FuncLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ L

/-- ### 在某处可导
    ### Derivable at Some Point -/
abbrev isDerivableAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, Deriv F x₀ L

/-- ### 处处可导
    ### Derivable Everywhere -/
abbrev isDerivable (F : Function) : Prop :=
  ∀ x ∈ F.domain, ∃ L : ℝ, Deriv F x L

open Classical in
/-- ### 微分算子
    ### Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def Diff (F : Function) : Function where
  map := fun x =>
    if h : isDerivableAt F x then
      Classical.choose h
    else 0
  domain := { x | isDerivableAt F x }

/-- ### n阶微分算子
    ### N-th Order Differential Operator
    - Note that derivative function's domain may be smaller than that of the
      original function, or **even empty** -/
noncomputable def NthDiff (n : ℕ) (F : Function) : Function :=
  match n with
  | 0     => F
  | n + 1 => Diff (NthDiff n F)

/-- ### n阶导数
    ### N-th Order Derivative -/
def NthDeriv (n : ℕ) (F : Function) (x₀ L : ℝ) : Prop :=
  match n with
  | 0     => F.map x₀ = L ∧ x₀ ∈ F.domain
  | n + 1 => Deriv (NthDiff n F) x₀ L

/-- ### 在某处n阶可导
    ### N-th Order Derivable at Some Point -/
abbrev isNthDerivableAt (n : ℕ) (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, NthDeriv n F x₀ L

/-- ### n阶可导
    ### N-th Order Derivable -/
abbrev isNthDerivable (n : ℕ) (F : Function) : Prop :=
  ∀ x ∈ F.domain, ∃ L : ℝ, NthDeriv n F x L

/-- ### 左导数
    ### Left Derivative -/
def LeftDeriv (F : Function) (x₀ L : ℝ) : Prop :=
  LeftLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ L

/-- ### 在某处左可导
    ### Left Derivable at Some Point -/
abbrev isLeftDerivableAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftDeriv F x₀ L

/-- ### 右导数
    ### Right Derivative -/
def RightDeriv (F : Function) (x₀ L : ℝ) : Prop :=
  RightLimit ((F - Constant (F.map x₀)) / (Identity - Constant x₀)) x₀ L

/-- ### 在某处右可导
    ### Right Derivable at Some Point -/
abbrev isRightDerivableAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightDeriv F x₀ L


/- ## 导数的性质 Properties of Derivative -/

/-- ### 可导 ⇒ 连续
    ### Derivable ⇒ Continuous -/
theorem Derivable.isContinuousAt {F : Function} {x₀ : ℝ}
    (h_deriv : isDerivableAt F x₀)
  : isContinuousAt F x₀
:= sorry
