import «Calculus@JokerXin».Prelude


/- ## 函数的定义 Definition of Function -/

/-- ### 函数
    ### Function
    A Real function with domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain, respectively -/
structure Function where
  map : ℝ → ℝ
  domain : Set ℝ


/- ## 函数运算的定义 Definitions of Function Operations -/

/-- ### 自由一元运算
    ### Free Unary Operation -/
def Function_Free₁ (F : Function) (op₁ : ℝ → ℝ) : Function :=
  ⟨(fun x ↦ op₁ (F.map x)), F.domain⟩

/-- ### 自由二元运算
    ### Free Binary Operation -/
def Function_Free₂ (F G : Function) (op₂ : ℝ → ℝ → ℝ) : Function :=
  ⟨(fun x ↦ op₂ (F.map x) (G.map x)), F.domain ∩ G.domain⟩

/-- ### 数乘
    ### Scalar Multiplication -/
def Function_SMul (k : ℝ) (F : Function) : Function :=
  ⟨k • F.map, F.domain⟩

/-- ### 乘法幂
    ### Multiplication Power -/
def Function_MPow (F : Function) (n : ℕ) : Function :=
  ⟨(fun x ↦ (F.map x)^n), F.domain⟩

/-- ### 复合
    ### Composition -/
def Function_Comp (F G : Function) : Function :=
  ⟨(fun x ↦ F.map (G.map x)), F.domain ∩ G.domain⟩

instance : Add Function where
  add := (Function_Free₂ · · (· + ·))
instance : Sub Function where
  sub := (Function_Free₂ · · (· - ·))
instance : Mul Function where
  mul := (Function_Free₂ · · (· * ·))
noncomputable instance : Div Function where
  div F G := ⟨
    (fun x ↦ F.map x / G.map x),
    F.domain ∩ G.domain ∩ { x : ℝ | G.map x ≠ 0}
  ⟩
/- # To be Modified ↓ -/
noncomputable instance : HomogeneousPow Function where
  pow := (Function_Free₂ · · (· ^ ·))
instance : SMul ℝ Function where
  smul := Function_SMul
instance : NatPow Function where
  pow := Function_MPow

infixr:90 " ⊙ " => (Function_Comp · ·)


/- ## 基本函数 Fundamental Functions -/

/-- ### 常函数
    ### Constant Function -/
def Constant (C : ℝ) : Function := ⟨(fun _ ↦ C), Iii⟩

/-- ### 恒等函数
    ### Identity Function -/
def Identity : Function := ⟨(·), Iii⟩

/-- ### 绝对值函数
    ### Absolute Value Function
    - from `Mathlib.Algebra.Order.Group.Unbundled.Abs` (by `to_additive`) -/
def Abs : Function := ⟨(|·|), Iii⟩

/-- ### 幂函数
    ### Power Function -/
/- # To be Modified ↓ -/
noncomputable def Power (a : ℝ) : Function := ⟨(·^a), Iii⟩

/-- ### 平方根函数
    ### Square Root Function
    - from `Mathlib.Analysis.Real.Sqrt` -/
noncomputable def Sqrt : Function := ⟨(√·), Ici 0⟩

/-- ### 自然指数函数
    ### Natural Exponential Function
    - from `Mathlib.Analysis.Complex.Exponential` -/
noncomputable def Exp : Function := ⟨exp, Iii⟩

/-- ### 自然对数函数
    ### Natural Logarithm Function
    - from `Mathlib.Analysis.SpecialFunctions.Log.Basic` -/
noncomputable def Ln : Function := ⟨ln, Ioi 0⟩

/-- ### 正弦函数
    ### Sine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Sin : Function := ⟨sin, Iii⟩

/-- ### 余弦函数
    ### Cosine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Cos : Function := ⟨cos, Iii⟩

/-- ### 正切函数
    ### Tangent Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Tan : Function := ⟨tan, { x : ℝ | ¬ ∃ k : ℤ, x = π / 2 + k * π }⟩

/-- ### 余切函数
    ### Cotangent Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Cot : Function := ⟨cot, { x : ℝ | ¬ ∃ k : ℤ, x = k * π }⟩

/-- ### 正割函数
    ### Secant Function -/
noncomputable def Sec : Function := Constant 1 / Cos

/-- ### 余割函数
    ### Cosecant Function -/
noncomputable def Csc : Function := Constant 1 / Sin

/-- ### 双曲正弦函数
    ### Hyp-Sine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Sinh : Function := ⟨sinh, Iii⟩

/-- ### 双曲余弦函数
    ### Hyp-Cosine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Cosh : Function := ⟨cosh, Iii⟩

/-- ### 双曲正切函数
    ### Hyp-Tangent Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
noncomputable def Tanh : Function := ⟨tanh, Iii⟩

/-- ### 双曲余切函数
    ### Hyp-Cotangent Function -/
noncomputable def Coth : Function := Constant 1 / Tanh

/-- ### 双曲正割函数
    ### Hyp-Secant Function -/
noncomputable def Sech : Function := ⟨sech, Iii⟩

/-- ### 双曲余割函数
    ### Hyp-Cosecant Function -/
noncomputable def Csch : Function := Constant 1 / Sinh

/-- ### 反正弦函数
    ### Arc-Sine Function
    - from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` -/
noncomputable def Arcsin : Function := ⟨arcsin, Icc (-1) 1⟩

/-- ### 反余弦函数
    ### Arc-Cosine Function
    - from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` -/
noncomputable def Arccos : Function := ⟨arccos, Icc (-1) 1⟩

/-- ### 反正切函数
    ### Arc-Tangent Function
    - from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan` -/
noncomputable def Arctan : Function := ⟨arctan, Iii⟩

/-- ### 反余切函数
    ### Arc-Cotangent Function -/
noncomputable def Arccot : Function := ⟨arccot, Iii⟩

/-- ### 反正割函数
    ### Arc-Secant Function -/
noncomputable def Arcsec : Function := Arccos ⊙ (Constant 1 / Identity)

/-- ### 反余割函数
    ### Arc-Cosecant Function -/
noncomputable def Arccsc : Function := Arcsin ⊙ (Constant 1 / Identity)
