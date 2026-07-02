import «Calculus@JokerXin».Function.Differential.Defs
import «Calculus@JokerXin».Expr.UndeterminedEqual


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

open Classical in
/-- ### n阶导数表达式
    ### N-th Order Derivative Expression -/
def NthDerivExpr (n : ℕ) (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : isNthDerivableAt n ⟨f, Iii⟩ x₀ then
    the (choose h)
  else none

macro "D" : term => `(DerivExpr)
macro "D₋" : term => `(LeftDerivExpr)
macro "D₊" : term => `(RightDerivExpr)
macro "Dₙ" : term => `(NthDerivExpr)

end

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

/-- ### n阶导数表达式的局部同余性
    ### N-th Order Derivative Expression's Local Congruence -/
lemma NthDerivExpr.Congr {n : ℕ} {x₀ : ℝ} {f g : ℝ → ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : Dₙ n f x₀ =? Dₙ n g x₀
:= sorry

open Classical in
theorem DerivExpr_to_Deriv {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : D f x₀ = the A)
  : Deriv ⟨f, Iii⟩ x₀ A
:= by
  unfold DerivExpr at h_deriv
  split at h_deriv
  · rename_i h_derivable
    injection h_deriv with h_val_eq
    rw [← h_val_eq]
    exact choose_spec h_derivable
  · contradiction

open Classical in
theorem Deriv_to_DerivExpr {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : Deriv ⟨f, Iii⟩ x₀ A)
  : D f x₀ = the A
:= by
  unfold DerivExpr
  have h_derivable : isDerivableAt ⟨f, Iii⟩ x₀ := ⟨A, h_deriv⟩
  simp only [dif_pos h_derivable]
  apply congrArg the
  exact FuncLimit_Unique (choose_spec h_derivable) h_deriv

open Classical in
theorem LeftDerivExpr_to_LeftDeriv {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : D₋ f x₀ = the A)
  : LeftDeriv ⟨f, Iii⟩ x₀ A
:= by
  unfold LeftDerivExpr at h_deriv
  split at h_deriv
  · rename_i h_derivable
    injection h_deriv with h_val_eq
    rw [← h_val_eq]
    exact choose_spec h_derivable
  · contradiction

open Classical in
theorem LeftDeriv_to_LeftDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : LeftDeriv ⟨f, Iii⟩ x₀ A)
  : D₋ f x₀ = the A
:= by
  unfold LeftDerivExpr
  have h_derivable : isLeftDerivableAt ⟨f, Iii⟩ x₀ := ⟨A, h_deriv⟩
  simp only [dif_pos h_derivable]
  apply congrArg the
  exact LeftLimit_Unique (choose_spec h_derivable) h_deriv

open Classical in
theorem RightDerivExpr_to_RightDeriv {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : D₊ f x₀ = the A)
  : RightDeriv ⟨f, Iii⟩ x₀ A
:= by
  unfold RightDerivExpr at h_deriv
  split at h_deriv
  · rename_i h_derivable
    injection h_deriv with h_val_eq
    rw [← h_val_eq]
    exact choose_spec h_derivable
  · contradiction

open Classical in
theorem RightDeriv_to_RightDerivExpr {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : RightDeriv ⟨f, Iii⟩ x₀ A)
  : D₊ f x₀ = the A
:= by
  unfold RightDerivExpr
  have h_derivable : isRightDerivableAt ⟨f, Iii⟩ x₀ := ⟨A, h_deriv⟩
  simp only [dif_pos h_derivable]
  apply congrArg the
  exact RightLimit_Unique (choose_spec h_derivable) h_deriv

open Classical in
theorem NthDerivExpr_to_NthDeriv {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : Dₙ n f x₀ = the A)
  : NthDeriv n ⟨f, Iii⟩ x₀ A
:= by
  unfold NthDerivExpr at h_deriv
  split at h_deriv
  · rename_i h_derivable
    injection h_deriv with h_val_eq
    rw [← h_val_eq]
    exact choose_spec h_derivable
  · contradiction

open Classical in
theorem NthDeriv_to_NthDerivExpr {n : ℕ} {f : ℝ → ℝ} {x₀ A : ℝ}
    (h_deriv : NthDeriv n ⟨f, Iii⟩ x₀ A)
  : Dₙ n f x₀ = the A
:= sorry
