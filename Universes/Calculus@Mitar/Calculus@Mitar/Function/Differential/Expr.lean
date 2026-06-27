import «Calculus@Mitar».Function.Differential.Defs
import «Calculus@Mitar».Expr.UndeterminedEqual


/- All the derivative conclusions related to calculations ought to be presented in the form
    of expressions. -/

/- ## 导数表达式 Derivative Expression -/

noncomputable section

open Classical in
/-- ### 导数表达式
    ### Derivative Expression -/
def DerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isDerivableAt ⟨f, Iii⟩ x₀ then
    the (choose h)
  else none

open Classical in
/-- ### 左导数表达式
    ### Left Derivative Expression -/
def LeftDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isLeftDerivableAt ⟨f, Iii⟩ x₀ then
    the (choose h)
  else none

open Classical in
/-- ### 右导数表达式
    ### Right Derivative Expression -/
def RightDerivExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isRightDerivableAt ⟨f, Iii⟩ x₀ then
    the (choose h)
  else none

macro "D" : term => `(DerivExpr)
macro "D₋" : term => `(LeftDerivExpr)
macro "D₊" : term => `(RightDerivExpr)

end

open Classical in
@[aesop safe apply (rule_sets := [InitializeExpr])]
theorem DerivExpr_isDeriv {F : Function} {x₀ L : ℝ}
    (h_lim : D F.map x₀ = the L)
  : Deriv F x₀ L
:= by
  unfold DerivExpr at h_lim
  split at h_lim
  next h_deriv =>
    injection h_lim with h_eq
    rw [← h_eq]
    exact choose_spec h_deriv
  next h_not_conv => contradiction

/-- ### 导数表达式的局部同余性
    ### Derivative Expression's Local Congruence -/
lemma DerivExpr.Congr {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : D f x₀ =? D g x₀
:= sorry

/-- ### 左导数表达式的局部同余性
    ### Left Derivative Expression's Local Congruence -/
lemma LeftDerivExpr.Congr {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : D₋ f x₀ =? D₋ g x₀
:= sorry

/-- ### 右导数表达式的局部同余性
    ### Right Derivative Expression's Local Congruence -/
lemma RightDerivExpr.Congr {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : D₊ f x₀ =? D₊ g x₀
:= sorry
