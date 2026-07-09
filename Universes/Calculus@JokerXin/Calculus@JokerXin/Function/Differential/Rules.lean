import «Calculus@JokerXin».Function.Differential.Expr


/- ## 导数运算法则 Derivative Calculation Rules -/

/-- ### 导数数乘
    ### Derivative Scalar Multiplication -/
theorem Deriv.SMul {F : Function} {k x₀ L : ℝ}
    (h_f : Deriv F x₀ L)
  : Deriv (k • F) x₀ (k * L)
:= sorry

/-- ### 导数数乘（表达式）
    ### Derivative Scalar Multiplication (Expression) -/
theorem DerivExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : D (k • f) x₀ =? the k * D f x₀
:= sorry

/-- ### 左导数数乘
    ### Left Derivative Scalar Multiplication -/
theorem LeftDeriv.SMul {F : Function} {k x₀ L : ℝ}
    (h_f : LeftDeriv F x₀ L)
  : LeftDeriv (k • F) x₀ (k * L)
:= sorry

/-- ### 左导数数乘（表达式）
    ### Left Derivative Scalar Multiplication (Expression) -/
theorem LeftDerivExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : D₋ (k • f) x₀ =? the k * D₋ f x₀
:= sorry

/-- ### 右导数数乘
    ### Right Derivative Scalar Multiplication -/
theorem RightDeriv.SMul {F : Function} {k x₀ L : ℝ}
    (h_f : RightDeriv F x₀ L)
  : RightDeriv (k • F) x₀ (k * L)
:= sorry

/-- ### 右导数数乘（表达式）
    ### Right Derivative Scalar Multiplication (Expression) -/
theorem RightDerivExpr.SMul {f : ℝ → ℝ} {k x₀ : ℝ}
  : D₊ (k • f) x₀ =? the k * D₊ f x₀
:= sorry

/-- ### n阶导数数乘
    ### N-th Order Derivative Scalar Multiplication -/
theorem NthDeriv.SMul {n : ℕ} {F : Function} {k x₀ L : ℝ}
    (h_f : NthDeriv n F x₀ L)
  : NthDeriv n (k • F) x₀ (k * L)
:= sorry

/-- ### n阶导数数乘（表达式）
    ### N-th Order Derivative Scalar Multiplication (Expression) -/
theorem NthDerivExpr.SMul {n : ℕ} {f : ℝ → ℝ} {k x₀ : ℝ}
  : Dₙ n (k • f) x₀ =? the k * Dₙ n f x₀
:= sorry

/-- ### 导数加法
    ### Derivative Addition -/
theorem Deriv.Add {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : Deriv F x₀ D1) (h_G : Deriv G x₀ D2)
  : Deriv (F + G) x₀ (D1 + D2)
:= sorry

/-- ### 导数加法（表达式）
    ### Derivative Addition (Expression) -/
theorem DerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f + g) x₀ =? D f x₀ + D g x₀
:= by
  cases h_A : D f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D g x₀ with
    | none => trivial
    | some B =>
      have h_f : Deriv ⟨f, Iii⟩ x₀ A :=
        DerivExpr_to_Deriv h_A
      have h_g : Deriv ⟨g, Iii⟩ x₀ B :=
        DerivExpr_to_Deriv h_B
      have h_fg_eq : D (f + g) x₀ = the (A + B) := by
        apply Deriv_to_DerivExpr
        convert Deriv.Add h_f h_g using 2
        simp only [HAdd.hAdd, Add.add, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 左导数加法
    ### Left Derivative Addition -/
theorem LeftDeriv.Add {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : LeftDeriv F x₀ D1) (h_G : LeftDeriv G x₀ D2)
  : LeftDeriv (F + G) x₀ (D1 + D2)
:= sorry

/-- ### 左导数加法（表达式）
    ### Left Derivative Addition (Expression) -/
theorem LeftDerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f + g) x₀ =? D₋ f x₀ + D₋ g x₀
:= by
  cases h_A : D₋ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D₋ g x₀ with
    | none => trivial
    | some B =>
      have h_f : LeftDeriv ⟨f, Iii⟩ x₀ A :=
        LeftDerivExpr_to_LeftDeriv h_A
      have h_g : LeftDeriv ⟨g, Iii⟩ x₀ B :=
        LeftDerivExpr_to_LeftDeriv h_B
      have h_fg_eq : D₋ (f + g) x₀ = the (A + B) := by
        apply LeftDeriv_to_LeftDerivExpr
        convert LeftDeriv.Add h_f h_g using 2
        simp only [HAdd.hAdd, Add.add, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 右导数加法
    ### Right Derivative Addition -/
theorem RightDeriv.Add {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : RightDeriv F x₀ D1) (h_G : RightDeriv G x₀ D2)
  : RightDeriv (F + G) x₀ (D1 + D2)
:= sorry

/-- ### 右导数加法（表达式）
    ### Right Derivative Addition (Expression) -/
theorem RightDerivExpr.Add {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f + g) x₀ =? D₊ f x₀ + D₊ g x₀
:= by
  cases h_A : D₊ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D₊ g x₀ with
    | none => trivial
    | some B =>
      have h_f : RightDeriv ⟨f, Iii⟩ x₀ A :=
        RightDerivExpr_to_RightDeriv h_A
      have h_g : RightDeriv ⟨g, Iii⟩ x₀ B :=
        RightDerivExpr_to_RightDeriv h_B
      have h_fg_eq : D₊ (f + g) x₀ = the (A + B) := by
        apply RightDeriv_to_RightDerivExpr
        convert RightDeriv.Add h_f h_g using 2
        simp only [HAdd.hAdd, Add.add, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### n阶导数加法
    ### N-th Order Derivative Addition -/
theorem NthDeriv.Add {n : ℕ} {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : NthDeriv n F x₀ D1) (h_G : NthDeriv n G x₀ D2)
  : NthDeriv n (F + G) x₀ (D1 + D2)
:= sorry

/-- ### n阶导数加法（表达式）
    ### N-th Order Derivative Addition (Expression) -/
theorem NthDerivExpr.Add {n : ℕ} {f g : ℝ → ℝ} {x₀ : ℝ}
  : Dₙ n (f + g) x₀ =? Dₙ n f x₀ + D g x₀
:= sorry

/-- ### 导数减法
    ### Derivative Subtraction -/
theorem Deriv.Sub {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : Deriv F x₀ D1) (h_G : Deriv G x₀ D2)
  : Deriv (F - G) x₀ (D1 - D2)
:= sorry

/-- ### 导数减法（表达式）
    ### Derivative Subtraction (Expression) -/
theorem DerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f - g) x₀ =? D f x₀ - D g x₀
:= by
  cases h_A : D f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D g x₀ with
    | none => trivial
    | some B =>
      have h_f : Deriv ⟨f, Iii⟩ x₀ A :=
        DerivExpr_to_Deriv h_A
      have h_g : Deriv ⟨g, Iii⟩ x₀ B :=
        DerivExpr_to_Deriv h_B
      have h_fg_eq : D (f - g) x₀ = the (A - B) := by
        apply Deriv_to_DerivExpr
        convert Deriv.Sub h_f h_g using 2
        simp only [HSub.hSub, Sub.sub, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 左导数减法
    ### Left Derivative Subtraction -/
theorem LeftDeriv.Sub {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : LeftDeriv F x₀ D1) (h_G : LeftDeriv G x₀ D2)
  : LeftDeriv (F - G) x₀ (A - B)
:= sorry

/-- ### 左导数减法（表达式）
    ### Left Derivative Subtraction (Expression) -/
theorem LeftDerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f - g) x₀ =? D₋ f x₀ - D₋ g x₀
:= by
  cases h_A : D₋ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D₋ g x₀ with
    | none => trivial
    | some B =>
      have h_f : LeftDeriv ⟨f, Iii⟩ x₀ A :=
        LeftDerivExpr_to_LeftDeriv h_A
      have h_g : LeftDeriv ⟨g, Iii⟩ x₀ B :=
        LeftDerivExpr_to_LeftDeriv h_B
      have h_fg_eq : D₋ (f - g) x₀ = the (A - B) := by
        apply LeftDeriv_to_LeftDerivExpr
        convert LeftDeriv.Sub h_f h_g using 2
        simp only [HSub.hSub, Sub.sub, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 右导数减法
    ### Right Derivative Subtraction -/
theorem RightDeriv.Sub {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : RightDeriv F x₀ D1) (h_G : RightDeriv G x₀ D2)
  : RightDeriv (F - G) x₀ (D1 - D2)
:= sorry

/-- ### 右导数减法（表达式）
    ### Right Derivative Subtraction (Expression) -/
theorem RightDerivExpr.Sub {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f - g) x₀ =? D₊ f x₀ - D₊ g x₀
:= by
  cases h_A : D₊ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D₊ g x₀ with
    | none => trivial
    | some B =>
      have h_f : RightDeriv ⟨f, Iii⟩ x₀ A :=
        RightDerivExpr_to_RightDeriv h_A
      have h_g : RightDeriv ⟨g, Iii⟩ x₀ B :=
        RightDerivExpr_to_RightDeriv h_B
      have h_fg_eq : D₊ (f - g) x₀ = the (A - B) := by
        apply RightDeriv_to_RightDerivExpr
        convert RightDeriv.Sub h_f h_g using 2
        simp only [HSub.hSub, Sub.sub, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### n阶导数减法
    ### N-th Order Derivative Subtraction -/
theorem NthDeriv.Sub {n : ℕ} {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : NthDeriv n F x₀ D1) (h_G : NthDeriv n G x₀ D2)
  : NthDeriv n (F - G) x₀ (D1 - D2)
:= sorry

/-- ### n阶导数减法（表达式）
    ### N-th Order Derivative Subtraction (Expression) -/
theorem NthDerivExpr.Sub {n : ℕ} {f g : ℝ → ℝ} {x₀ : ℝ}
  : Dₙ n (f - g) x₀ =? Dₙ n f x₀ - D g x₀
:= sorry

/-- ### 导数乘法
    ### Derivative Multiplication -/
theorem Deriv.Mul {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : Deriv F x₀ D1) (h_G : Deriv G x₀ D2)
  : Deriv (F * G) x₀ (D1 * G.map x₀ + F.map x₀ * D2)
:= sorry

/-- ### 导数乘法（表达式）
    ### Derivative Multiplication (Expression) -/
theorem DerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f * g) x₀ =? D f x₀ * the (g x₀) + the (f x₀) * D g x₀
:= by
  cases h_A : D f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D g x₀ with
    | none => trivial
    | some B =>
      have h_f : Deriv ⟨f, Iii⟩ x₀ A :=
        DerivExpr_to_Deriv h_A
      have h_g : Deriv ⟨g, Iii⟩ x₀ B :=
        DerivExpr_to_Deriv h_B
      have h_fg_eq : D (f * g) x₀ = the (A * g x₀ + f x₀ * B) := by
        apply Deriv_to_DerivExpr
        convert Deriv.Mul h_f h_g using 2
        simp only [HMul.hMul, Mul.mul, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 左导数乘法
    ### Left Derivative Multiplication -/
theorem LeftDeriv.Mul {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : LeftDeriv F x₀ D1) (h_G : LeftDeriv G x₀ D2)
  : LeftDeriv (F * G) x₀ (D1 * G.map x₀ + F.map x₀ * D2)
:= sorry

/-- ### 左导数乘法（表达式）
    ### Left Derivative Multiplication (Expression) -/
theorem LeftDerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f * g) x₀ =? D₋ f x₀ * the (g x₀) + the (f x₀) * D₋ g x₀
:= by
  cases h_A : D₋ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D₋ g x₀ with
    | none => trivial
    | some B =>
      have h_f : LeftDeriv ⟨f, Iii⟩ x₀ A :=
        LeftDerivExpr_to_LeftDeriv h_A
      have h_g : LeftDeriv ⟨g, Iii⟩ x₀ B :=
        LeftDerivExpr_to_LeftDeriv h_B
      have h_fg_eq : D₋ (f * g) x₀ = the (A * g x₀ + f x₀ * B) := by
        apply LeftDeriv_to_LeftDerivExpr
        convert LeftDeriv.Mul h_f h_g using 2
        simp only [HMul.hMul, Mul.mul, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 右导数乘法
    ### Right Derivative Multiplication -/
theorem RightDeriv.Mul {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : RightDeriv F x₀ D1) (h_G : RightDeriv G x₀ D2)
  : RightDeriv (F * G) x₀ (D1 * G.map x₀ + F.map x₀ * D2)
:= sorry

/-- ### 右导数乘法（表达式）
    ### Right Derivative Multiplication (Expression) -/
theorem RightDerivExpr.Mul {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f * g) x₀ =? D₊ f x₀ * the (g x₀) + the (f x₀) * D₊ g x₀
:= by
  cases h_A : D₊ f x₀ with
  | none => trivial
  | some A =>
    cases h_B : D₊ g x₀ with
    | none => trivial
    | some B =>
      have h_f : RightDeriv ⟨f, Iii⟩ x₀ A :=
        RightDerivExpr_to_RightDeriv h_A
      have h_g : RightDeriv ⟨g, Iii⟩ x₀ B :=
        RightDerivExpr_to_RightDeriv h_B
      have h_fg_eq : D₊ (f * g) x₀ = the (A * g x₀ + f x₀ * B) := by
        apply RightDeriv_to_RightDerivExpr
        convert RightDeriv.Mul h_f h_g using 2
        simp only [HMul.hMul, Mul.mul, Function_Free₂]
        rw [Set.inter_self]
      rw [h_fg_eq]
      rfl

/-- ### 导数除法
    ### Derivative Division -/
theorem Deriv.Div {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : Deriv F x₀ D1) (h_G : Deriv G x₀ D2)
    (h_g_ne_0 : G.map x₀ ≠ 0)
  : Deriv (F / G) x₀ ((D1 * G.map x₀ - F.map x₀ * D2) / (G.map x₀)^2)
:= sorry

/-- ### 导数除法（表达式）
    ### Derivative Division (Expression) -/
theorem DerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f / g) x₀ =? (D f x₀ * the (g x₀) - the (f x₀) * D g x₀) / the ((g x₀)^2)
:= sorry

/-- ### 左导数除法
    ### Left Derivative Division -/
theorem LeftDeriv.Div {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : LeftDeriv F x₀ D1) (h_G : LeftDeriv G x₀ D2)
    (h_g_ne_0 : G.map x₀ ≠ 0)
  : LeftDeriv (F / G) x₀ ((D1 * G.map x₀ - F.map x₀ * D2) / (G.map x₀)^2)
:= sorry

/-- ### 左导数除法（表达式）
    ### Left Derivative Division (Expression) -/
theorem LeftDerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f / g) x₀ =? (D₋ f x₀ * the (g x₀) - the (f x₀) * D₋ g x₀) / the ((g x₀)^2)
:= sorry

/-- ### 右导数除法
    ### Right Derivative Division -/
theorem RightDeriv.Div {F G : Function} {x₀ D1 D2 : ℝ}
    (h_F : RightDeriv F x₀ D1) (h_G : RightDeriv G x₀ D2)
    (h_g_ne_0 : G.map x₀ ≠ 0)
  : RightDeriv (F / G) x₀ ((D1 * G.map x₀ - F.map x₀ * D2) / (G.map x₀)^2)
:= sorry

/-- ### 右导数除法（表达式）
    ### Right Derivative Division (Expression) -/
theorem RightDerivExpr.Div {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f / g) x₀ =? (D₊ f x₀ * the (g x₀) - the (f x₀) * D₊ g x₀) / the ((g x₀)^2)
:= sorry

/-- ### 导数链式法则
    ### Derivative's Chain Rule -/
theorem Deriv.Chain {F G : Function} {x₀ F' G' : ℝ}
    (h_G : Deriv G x₀ G') (h_F : Deriv F (G.map x₀) F')
  : Deriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- ### 导数链式法则（表达式）
    ### Derivative's Chain Rule (Expression) -/
theorem DerivExpr.Chain {f g : ℝ → ℝ} {x₀ : ℝ}
  : D (f ∘ g) x₀ =? D f (g x₀) * D g x₀
:= sorry

/-- ### 左导数链式法则
    ### Left Derivative's Chain Rule -/
theorem LeftDeriv.Chain {F G : Function} {x₀ F' G' : ℝ}
    (h_G : LeftDeriv G x₀ G') (h_F : LeftDeriv F (G.map x₀) F')
  : LeftDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- ### 左导数链式法则（表达式）
    ### Left Derivative's Chain Rule (Expression) -/
theorem LeftDerivExpr.Chain {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₋ (f ∘ g) x₀ =? D₋ f (g x₀) * D₋ g x₀
:= sorry

/-- ### 右导数链式法则
    ### Right Derivative's Chain Rule -/
theorem RightDeriv.Chain {F G : Function} {x₀ F' G' : ℝ}
    (h_G : RightDeriv G x₀ G') (h_F : RightDeriv F (G.map x₀) F')
  : RightDeriv (F ⊙ G) x₀ (F' * G')
:= sorry

/-- ### 右导数链式法则（表达式）
    ### Right Derivative's Chain Rule (Expression) -/
theorem RightDerivExpr.Chain {f g : ℝ → ℝ} {x₀ : ℝ}
  : D₊ (f ∘ g) x₀ =? D₊ f (g x₀) * D₊ g x₀
:= sorry
