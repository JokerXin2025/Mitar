import «Calculus@JokerXin».Limit.Defs
import «Calculus@JokerXin».Limit.Expr
import Lean.Elab.Tactic.Basic


/- ## 基本极限 Basic Limits -/

/-- ### 常数列的极限（表达式）
    ### Constant Sequence's Limit (Expression) -/
@[aesop safe apply (rule_sets := [LimitBasic])]
lemma SeqLimitExpr.Constant {L : ℝ}
  : limₙ (fun _ ↦ L) = the L
:= sorry

/- For more limits, please refer to `Function.Continuity.Rules`. -/


/- ## 极限运算法则 Limit Calculation Rules -/

/-
/-  ### 数列极限数乘
    ### Sequence Limit Scalar Multiplication -/

/-- ### 数列极限数乘（表达式）
    ### Sequence Limit Scalar Multiplication (Expression) -/
theorem SeqLimitExpr.SMul {a : ℕ → ℝ} {k : ℝ}
  : limₙ (k • a) =? the k * limₙ a
:= sorry

/-- ### 函数极限数乘
    ### Function Limit Scalar Multiplication -/
theorem FuncLimit.SMul {F : Function} {k x₀ L : ℝ}
    (h_f : FuncLimit F x₀ L)
  : FuncLimit (k • F) x₀ (k * L)
:= sorry

/-- ### 函数极限数乘（表达式）
    ### Function Limit Scalar Multiplication (Expression) -/
theorem FuncLimitExpr.Smul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim (k • f) x₀ =? the k * lim f x₀
:= sorry

/-- ### 左极限数乘
    ### Left Limit Scalar Multiplication -/
theorem LeftLimit.SMul {F : Function} {k x₀ L : ℝ}
    (h_f : LeftLimit F x₀ L)
  : LeftLimit (k • F) x₀ (k * L)
:= sorry

/-- ### 左极限数乘（表达式）
    ### Left Limit Scalar Multiplication (Expression) -/
theorem LeftLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim₋ (k • f) x₀ =? the k * lim₋ f x₀
:= sorry

/-- ### 右极限数乘
    ### Right Limit Scalar Multiplication -/
theorem RightLimit.SMul {F G : Function} {k x₀ L : ℝ}
    (h_f : RightLimit F x₀ L)
  : RightLimit (k • F) x₀ (k * L)
:= sorry

/-- ### 右极限数乘（表达式）
    ### Right Limit Scalar Multiplication (Expression) -/
theorem RightLimitExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : lim₊ (k • f) x₀ =? the k * lim₊ f x₀
:= sorry
-/

/-- ### 数列极限加法
    ### Sequence Limit Addition -/
theorem SeqLimit.Add {A B : Sequence} {L1 L2 : ℝ}
    (h_A : SeqLimit A L1) (h_B : SeqLimit B L2)
  : SeqLimit (A + B) (L1 + L2)
:= sorry

/-- ### 数列极限加法（表达式）
    ### Sequence Limit Addition (Expression) -/
theorem SeqLimitExpr.Add {a b : ℕ → ℝ}
  : limₙ (a + b) =? limₙ a + limₙ b
:= sorry

/-- ### 函数极限加法
    ### Function Limit Addition -/
theorem FuncLimit.Add {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : FuncLimit F x₀ L1) (h_G : FuncLimit G x₀ L2)
  : FuncLimit (F + G) x₀ (L1 + L2)
:= sorry

/-- ### 函数极限加法（表达式）
    ### Function Limit Addition (Expression) -/
theorem FuncLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f + g) x₀ =? lim f x₀ + lim g x₀
:= by
  cases h_A : lim f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim g x₀ with
    | none => trivial
    | some B =>
      have h_f : FuncLimit ⟨f, Iii⟩ x₀ A :=
        FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : FuncLimit ⟨g, Iii⟩ x₀ B :=
        FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim (f + g) x₀ = the (A + B) := by
        apply FuncLimit_to_FuncLimitExpr
        exact FuncLimit.Add h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 左极限加法
    ### Left Limit Addition -/
theorem LeftLimit.Add {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : LeftLimit F x₀ L1) (h_G : LeftLimit G x₀ L2)
  : LeftLimit (F + G) x₀ (L1 + L2)
:= sorry

/-- ### 左极限加法（表达式）
    ### Left Limit Addition (Expression) -/
theorem LeftLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f + g) x₀ =? lim₋ f x₀ + lim₋ g x₀
:= by
  cases h_A : lim₋ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim₋ g x₀ with
    | none => trivial
    | some B =>
      have h_f : LeftLimit ⟨f, Iii⟩ x₀ A :=
        LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : LeftLimit ⟨g, Iii⟩ x₀ B :=
        LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim₋ (f + g) x₀ = the (A + B) := by
        apply LeftLimit_to_LeftLimitExpr
        exact LeftLimit.Add h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 右极限加法
    ### Right Limit Addition -/
theorem RightLimit.Add {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : RightLimit F x₀ L1) (h_G : RightLimit G x₀ L2)
  : RightLimit (F + G) x₀ (L1 + L2)
:= sorry

/-- ### 右极限加法（表达式）
    ### Right Limit Addition (Expression) -/
theorem RightLimitExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f + g) x₀ =? lim₊ f x₀ + lim₊ g x₀
:= by
  cases h_A : lim₊ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim₊ g x₀ with
    | none => trivial
    | some B =>
      have h_f : RightLimit ⟨f, Iii⟩ x₀ A :=
        RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : RightLimit ⟨g, Iii⟩ x₀ B :=
        RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim₊ (f + g) x₀ = the (A + B) := by
        apply RightLimit_to_RightLimitExpr
        exact RightLimit.Add h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 数列极限减法
    ### Sequence Limit Subtraction -/
theorem SeqLimit.Sub {A B : Sequence} {L1 L2 : ℝ}
    (h_A : SeqLimit A L1) (h_B : SeqLimit B L2)
  : SeqLimit (A - B) (L1 - L2)
:= sorry

/-- ### 数列极限减法（表达式）
    ### Sequence Limit Subtraction (Expression) -/
theorem SeqLimitExpr.Sub {a b : ℕ → ℝ}
  : limₙ (a - b) =? limₙ a - limₙ b
:= sorry

/-- ### 函数极限减法
    ### Function Limit Subtraction -/
theorem FuncLimit.Sub {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : FuncLimit F x₀ L1) (h_G : FuncLimit G x₀ L2)
  : FuncLimit (F - G) x₀ (L1 - L2)
:= sorry

/-- ### 函数极限减法（表达式）
    ### Function Limit Subtraction (Expression) -/
theorem FuncLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f - g) x₀ =? lim f x₀ - lim g x₀
:= by
  cases h_A : lim f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim g x₀ with
    | none => trivial
    | some B =>
      have h_f : FuncLimit ⟨f, Iii⟩ x₀ A :=
        FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : FuncLimit ⟨g, Iii⟩ x₀ B :=
        FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim (f - g) x₀ = the (A - B) := by
        apply FuncLimit_to_FuncLimitExpr
        exact FuncLimit.Sub h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 左极限减法
    ### Left Limit Subtraction -/
theorem LeftLimit.Sub {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : LeftLimit F x₀ L1) (h_G : LeftLimit G x₀ L2)
  : LeftLimit (F - G) x₀ (L1 - L2)
:= sorry

/-- ### 左极限减法（表达式）
    ### Left Limit Subtraction (Expression) -/
theorem LeftLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f - g) x₀ =? lim₋ f x₀ - lim₋ g x₀
:= by
  cases h_A : lim₋ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim₋ g x₀ with
    | none => trivial
    | some B =>
      have h_f : LeftLimit ⟨f, Iii⟩ x₀ A :=
        LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : LeftLimit ⟨g, Iii⟩ x₀ B :=
        LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim₋ (f - g) x₀ = the (A - B) := by
        apply LeftLimit_to_LeftLimitExpr
        exact LeftLimit.Sub h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 右极限减法
    ### Right Limit Subtraction -/
theorem RightLimit.Sub {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : RightLimit F x₀ L1) (h_G : RightLimit G x₀ L2)
  : RightLimit (F - G) x₀ (L1 - L2)
:= sorry

/-- ### 右极限减法（表达式）
    ### Right Limit Subtraction (Expression) -/
theorem RightLimitExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f - g) x₀ =? lim₊ f x₀ - lim₊ g x₀
:= by
  cases h_A : lim₊ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim₊ g x₀ with
    | none => trivial
    | some B =>
      have h_f : RightLimit ⟨f, Iii⟩ x₀ A :=
        RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : RightLimit ⟨g, Iii⟩ x₀ B :=
        RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim₊ (f - g) x₀ = the (A - B) := by
        apply RightLimit_to_RightLimitExpr
        exact RightLimit.Sub h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 数列极限乘法
    ### Sequence Limit Multiplication -/
theorem SeqLimit.Mul {A B : Sequence} {L1 L2 : ℝ}
    (h_A : SeqLimit A L1) (h_B : SeqLimit B L2)
  : SeqLimit (A * B) (L1 * L2)
:= sorry

/-- ### 数列极限乘法（表达式）
    ### Sequence Limit Multiplication (Expression) -/
theorem SeqLimitExpr.Mul {a b : ℕ → ℝ}
  : limₙ (a * b) =? limₙ a * limₙ b
:= sorry

/-- ### 函数极限乘法
    ### Function Limit Multiplication -/
theorem FuncLimit.Mul {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : FuncLimit F x₀ L1) (h_G : FuncLimit G x₀ L2)
  : FuncLimit (F * G) x₀ (L1 * L2)
:= sorry

/-- ### 函数极限乘法（表达式）
    ### Function Limit Multiplication (Expression) -/
theorem FuncLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f * g) x₀ =? lim f x₀ * lim g x₀
:= by
  cases h_A : lim f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim g x₀ with
    | none => trivial
    | some B =>
      have h_f : FuncLimit ⟨f, Iii⟩ x₀ A :=
        FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : FuncLimit ⟨g, Iii⟩ x₀ B :=
        FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim (f * g) x₀ = the (A * B) := by
        apply FuncLimit_to_FuncLimitExpr
        exact FuncLimit.Mul h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 左极限乘法
    ### Left Limit Multiplication -/
theorem LeftLimit.Mul {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : LeftLimit F x₀ L1) (h_G : LeftLimit G x₀ L2)
  : LeftLimit (F * G) x₀ (L1 * L2)
:= sorry

/-- ### 左极限乘法（表达式）
    ### Left Limit Multiplication (Expression) -/
theorem LeftLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f * g) x₀ =? lim₋ f x₀ * lim₋ g x₀
:= by
  cases h_A : lim₋ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim₋ g x₀ with
    | none => trivial
    | some B =>
      have h_f : LeftLimit ⟨f, Iii⟩ x₀ A :=
        LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : LeftLimit ⟨g, Iii⟩ x₀ B :=
        LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim₋ (f * g) x₀ = the (A * B) := by
        apply LeftLimit_to_LeftLimitExpr
        exact LeftLimit.Mul h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 右极限乘法
    ### Right Limit Multiplication -/
theorem RightLimit.Mul {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : RightLimit F x₀ L1) (h_G : RightLimit G x₀ L2)
  : RightLimit (F * G) x₀ (L1 * L2)
:= sorry

/-- ### 右极限乘法（表达式）
    ### Right Limit Multiplication (Expression) -/
theorem RightLimitExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f * g) x₀ =? lim₊ f x₀ * lim₊ g x₀
:= by
  cases h_A : lim₊ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : lim₊ g x₀ with
    | none => trivial
    | some B =>
      have h_f : RightLimit ⟨f, Iii⟩ x₀ A :=
        RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_A
      have h_g : RightLimit ⟨g, Iii⟩ x₀ B :=
        RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_B
      have h_fg_eq : lim₊ (f * g) x₀ = the (A * B) := by
        apply RightLimit_to_RightLimitExpr
        exact RightLimit.Mul h_f h_g
      rw [h_fg_eq]
      rfl

/-- ### 数列极限除法
    ### Sequence Limit Division -/
theorem SeqLimit.Div {A B : Sequence} {L1 L2 : ℝ}
    (h_A : SeqLimit A L1) (h_B : SeqLimit B L2)
    (h_B_ne_0 : L2 ≠ 0)
  : SeqLimit (A / B) (L1 / L2)
:= sorry

/-- ### 数列极限除法（表达式）
    ### Sequence Limit Division (Expression) -/
theorem SeqLimitExpr.Div {a b : ℕ → ℝ}
  : limₙ (a / b) =? limₙ a / limₙ b
:= sorry

/-- ### 函数极限除法
    ### Function Limit Division -/
theorem FuncLimit.Div {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : FuncLimit F x₀ L1) (h_G : FuncLimit G x₀ L2)
    (h_B_ne_0 : L2 ≠ 0)
  : FuncLimit (F / G) x₀ (L1 / L2)
:= sorry

/-- ### 函数极限除法（表达式）
    ### Function Limit Division (Expression) -/
theorem FuncLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim (f / g) x₀ =? lim f x₀ / lim g x₀
:= sorry/-by
  cases h_A : lim f x₀ with
  | none =>
    cases h_B : lim g x₀ with
    | none =>
      have h_rhs : (none : Option ℝ) / none = none := by
        have hB_neq : (none : Option ℝ) ≠ the 0 := by trivial
        simp only [HDiv.hDiv, Div.div, hB_neq]
        rfl
      rw [h_rhs]
      trivial
    | some B =>
      by_cases h_B0 : B = 0
      · have h_rhs : (none : Option ℝ) / some B = none := by
          have hB_eq : (some B : Option ℝ) = the 0 := by rw [h_B0]
          simp only [HDiv.hDiv, Div.div, hB_eq, ↓reduceIte]
        rw [h_rhs]
        trivial
      · have h_rhs : (none : Option ℝ) / some B = none := by
          have hB_neq : (some B : Option ℝ) ≠ the 0 := by
            intro h
            injection h with h'
            exact h_B0 h'
          simp only [HDiv.hDiv, Div.div, hB_neq]
          rfl
        rw [h_rhs]
        trivial
  | some A =>
    cases h_B : lim g x₀ with
    | none =>
      have h_rhs : (some A : Option ℝ) / none = none := by
        have hB_neq : (none : Option ℝ) ≠ the 0 := by trivial
        simp only [HDiv.hDiv, Div.div, hB_neq]
        rfl
      rw [h_rhs]
      trivial
    | some B =>
      by_cases h_B0 : B = 0
      · have h_rhs : (some A : Option ℝ) / some B = none := by
          have hB_eq : (some B : Option ℝ) = the 0 := by rw [h_B0]
          simp only [HDiv.hDiv, Div.div, hB_eq, ↓reduceIte]
        rw [h_rhs]
        trivial
      · have h_rhs : (some A : Option ℝ) / some B = the (A / B) := by
          have hB_neq : (some B : Option ℝ) ≠ the 0 := by
            intro h
            injection h with h'
            exact h_B0 h'
          simp only [HDiv.hDiv, Div.div, hB_neq]
          rfl
        rw [h_rhs]
        have h_f : FuncLimit ⟨f, Iii⟩ x₀ A :=
          FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_A
        have h_g : FuncLimit ⟨g, Iii⟩ x₀ B :=
          FuncLimitExpr_to_FuncLimit ⟨1, by norm_num, subset_univ _⟩ h_B
        have h_fg_eq : lim (f / g) x₀ = the (A / B) := by
          apply FuncLimit_to_FuncLimitExpr
          exact FuncLimit.Div h_f h_g h_B0
        rw [h_fg_eq]-/

/-- ### 左极限除法
    ### Left Limit Division -/
theorem LeftLimit.Div {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : LeftLimit F x₀ L1) (h_G : LeftLimit G x₀ L2)
    (h_B_ne_0 : L2 ≠ 0)
  : LeftLimit (F / G) x₀ (L1 / L2)
:= sorry

/-- ### 左极限除法（表达式）
    ### Left Limit Division (Expression) -/
theorem LeftLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ (f / g) x₀ =? lim₋ f x₀ / lim₋ g x₀
:= sorry/-by
  cases h_A : lim₋ f x₀ with
  | none =>
    cases h_B : lim₋ g x₀ with
    | none =>
      have h_rhs : (none : Option ℝ) / none = none := by
        have hB_neq : (none : Option ℝ) ≠ the 0 := by trivial
        simp only [HDiv.hDiv, Div.div, hB_neq]
        rfl
      rw [h_rhs]
      trivial
    | some B =>
      by_cases h_B0 : B = 0
      · have h_rhs : (none : Option ℝ) / some B = none := by
          have hB_eq : (some B : Option ℝ) = the 0 := by rw [h_B0]
          simp only [HDiv.hDiv, Div.div, hB_eq, ↓reduceIte]
        rw [h_rhs]
        trivial
      · have h_rhs : (none : Option ℝ) / some B = none := by
          have hB_neq : (some B : Option ℝ) ≠ the 0 := by
            intro h
            injection h with h'
            exact h_B0 h'
          simp only [HDiv.hDiv, Div.div, hB_neq]
          rfl
        rw [h_rhs]
        trivial
  | some A =>
    cases h_B : lim₋ g x₀ with
    | none =>
      have h_rhs : (some A : Option ℝ) / none = none := by
        have hB_neq : (none : Option ℝ) ≠ the 0 := by trivial
        simp only [HDiv.hDiv, Div.div, hB_neq]
        rfl
      rw [h_rhs]
      trivial
    | some B =>
      by_cases h_B0 : B = 0
      · have h_rhs : (some A : Option ℝ) / some B = none := by
          have hB_eq : (some B : Option ℝ) = the 0 := by rw [h_B0]
          simp only [HDiv.hDiv, Div.div, hB_eq, ↓reduceIte]
        rw [h_rhs]
        trivial
      · have h_rhs : (some A : Option ℝ) / some B = the (A / B) := by
          have hB_neq : (some B : Option ℝ) ≠ the 0 := by
            intro h
            injection h with h'
            exact h_B0 h'
          simp only [HDiv.hDiv, Div.div, hB_neq]
          rfl
        rw [h_rhs]
        have h_f : LeftLimit ⟨f, Iii⟩ x₀ A :=
          LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_A
        have h_g : LeftLimit ⟨g, Iii⟩ x₀ B :=
          LeftLimitExpr_to_LeftLimit ⟨1, by norm_num, subset_univ _⟩ h_B
        have h_fg_eq : lim₋ (f / g) x₀ = the (A / B) := by
          apply LeftLimit_to_LeftLimitExpr
          exact LeftLimit.Div h_f h_g h_B0
        rw [h_fg_eq]-/

/-- ### 右极限除法
    ### Right Limit Division -/
theorem RightLimit.Div {F G : Function} {x₀ L1 L2 : ℝ}
    (h_F : RightLimit F x₀ L1) (h_G : RightLimit G x₀ L2)
    (h_B_ne_0 : L2 ≠ 0)
  : RightLimit (F / G) x₀ (L1 / L2)
:= sorry

/-- ### 右极限除法（表达式）
    ### Right Limit Division (Expression) -/
theorem RightLimitExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ (f / g) x₀ =? lim₊ f x₀ / lim₊ g x₀
:= sorry/-by
  cases h_A : lim₊ f x₀ with
  | none =>
    cases h_B : lim₊ g x₀ with
    | none =>
      have h_rhs : (none : Option ℝ) / none = none := by
        have hB_neq : (none : Option ℝ) ≠ the 0 := by trivial
        simp only [HDiv.hDiv, Div.div, hB_neq]
        rfl
      rw [h_rhs]
      trivial
    | some B =>
      by_cases h_B0 : B = 0
      · have h_rhs : (none : Option ℝ) / some B = none := by
          have hB_eq : (some B : Option ℝ) = the 0 := by rw [h_B0]
          simp only [HDiv.hDiv, Div.div, hB_eq, ↓reduceIte]
        rw [h_rhs]
        trivial
      · have h_rhs : (none : Option ℝ) / some B = none := by
          have hB_neq : (some B : Option ℝ) ≠ the 0 := by
            intro h
            injection h with h'
            exact h_B0 h'
          simp only [HDiv.hDiv, Div.div, hB_neq]
          rfl
        rw [h_rhs]
        trivial
  | some A =>
    cases h_B : lim₊ g x₀ with
    | none =>
      have h_rhs : (some A : Option ℝ) / none = none := by
        have hB_neq : (none : Option ℝ) ≠ the 0 := by trivial
        simp only [HDiv.hDiv, Div.div, hB_neq]
        rfl
      rw [h_rhs]
      trivial
    | some B =>
      by_cases h_B0 : B = 0
      · have h_rhs : (some A : Option ℝ) / some B = none := by
          have hB_eq : (some B : Option ℝ) = the 0 := by rw [h_B0]
          simp only [HDiv.hDiv, Div.div, hB_eq, ↓reduceIte]
        rw [h_rhs]
        trivial
      · have h_rhs : (some A : Option ℝ) / some B = the (A / B) := by
          have hB_neq : (some B : Option ℝ) ≠ the 0 := by
            intro h
            injection h with h'
            exact h_B0 h'
          simp only [HDiv.hDiv, Div.div, hB_neq]
          rfl
        rw [h_rhs]
        have h_f : RightLimit ⟨f, Iii⟩ x₀ A :=
          RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_A
        have h_g : RightLimit ⟨g, Iii⟩ x₀ B :=
          RightLimitExpr_to_RightLimit ⟨1, by norm_num, subset_univ _⟩ h_B
        have h_fg_eq : lim₊ (f / g) x₀ = the (A / B) := by
          apply RightLimit_to_RightLimitExpr
          exact RightLimit.Div h_f h_g h_B0
        rw [h_fg_eq]-/

/-- ### 函数极限复合
    ### Function Limit Composition -/
theorem FuncLimit.Comp {x₀ u₀ L : ℝ} {F G : Function}
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_G_ne_u₀ : ∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, G.map x ≠ u₀)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_L : FuncLimit F u₀ L)
  : FuncLimit (F ⊙ G) x₀ L
:= sorry

/-- ### 夹逼定理（数列极限）
    ### Squeeze Theorem (Sequence Limit) -/
theorem SeqLimitSqueeze {a b c : ℕ → ℝ} {L : ℝ}
    (h_a : limₙ a = the L) (h_c : limₙ c = the L)
    (h_chain : ∀ n, a n ≤ b n ∧ b n ≤ c n)
  : limₙ b = the L
:= sorry

/-- ### 夹逼定理（函数极限）
    ### Squeeze Theorem (Function Limit) -/
theorem FuncLimitSqueeze {f g h : ℝ → ℝ} {x₀ L : ℝ}
    (h_f : lim f x₀ = the L) (h_h : lim h x₀ = the L)
    (h_chain : ∀ x, f x ≤ g x ∧ g x ≤ h x)
  : lim g x₀ = the L
:= sorry
