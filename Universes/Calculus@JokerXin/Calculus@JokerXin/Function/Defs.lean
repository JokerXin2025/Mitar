import «Calculus@JokerXin».Prelude


/- ## 函数的定义 Definitions of Function -/

/-- ### 函数
    ### Function
    A Real function with domain
    - `F.map` and `F.domain` refer to `F`'s total map and domain -/
structure Function where
  map : ℝ → ℝ
  domain : Set ℝ


/- ## 基本函数 Fundamental Functions -/

/-- ### 常函数
    ### Constant Function -/
def Constant (C : ℝ) : Function := ⟨(fun _ ↦ C), Iii⟩

/-- ### 恒等函数
    ### Identity Function -/
def Identity : Function := ⟨(·), Iii⟩

noncomputable section

/-- ### 幂函数
    ### Power Function -/
def Power (a : ℝ) : Function := ⟨(fun x ↦ x^a), Iii⟩

/-- ### 平方根函数
    ### Square Root Function
    - from `Mathlib.Analysis.Real.Sqrt` -/
def Sqrt : Function := ⟨(√·), Ici 0⟩

/-- ### 绝对值函数
    ### Absolute Value Function
    - from `Mathlib.Algebra.Order.Group.Unbundled.Abs` (by `to_additive`) -/
def Abs : Function := ⟨abs, Iii⟩

/-- ### 自然指数函数
    ### Natural Exponential Function
    - from `Mathlib.Analysis.Complex.Exponential` -/
def Exp : Function := ⟨exp, Iii⟩

/-- ### 自然对数函数
    ### Natural Logarithm Function
    - from `Mathlib.Analysis.SpecialFunctions.Log.Basic` -/
def Ln : Function := ⟨log, Ioi 0⟩

/-- ### 正弦函数
    ### Sine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Sin : Function := ⟨sin, Iii⟩

/-- ### 余弦函数
    ### Cosine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Cos : Function := ⟨cos, Iii⟩

/-- ### 正切函数
    ### Tangent Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Tan : Function := ⟨tan, { x : ℝ | ¬ ∃ k : ℤ, x = π / 2 + k * π }⟩

/-- ### 余切函数
    ### Cotangent Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Cot : Function := ⟨cot, { x : ℝ | ¬ ∃ k : ℤ, x = k * π }⟩

/-- ### 双曲正弦函数
    ### Hyperbolic Sine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Sinh : Function := ⟨sinh, Iii⟩

/-- ### 双曲余弦函数
    ### Hyperbolic Cosine Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Cosh : Function := ⟨cosh, Iii⟩

/-- ### 双曲正切函数
    ### Hyperbolic Tangent Function
    - from `Mathlib.Analysis.Complex.Trigonometric` -/
def Tanh : Function := ⟨tanh, Iii⟩

/-- ### 反正弦函数
    ### Arcsine Function
    - from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` -/
def Arcsin : Function := ⟨arcsin, Icc (-1) 1⟩

/-- ### 反余弦函数
    ### Arccosine Function
    - from `Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` -/
def Arccos : Function := ⟨arccos, Icc (-1) 1⟩

end


/- ## 函数运算的定义 Definitions of Function Operations -/

/-- ### 函数的一元运算
    ### Function's Unary Operation -/
def Function_op₁ (F : Function) (op : ℝ → ℝ) : Function :=
  ⟨(fun x ↦ op (F.map x)), F.domain⟩

/-- ### 函数的二元运算
    ### Function's Binary Operation -/
def Function_op₂ (F G : Function) (op : ℝ → ℝ → ℝ) : Function :=
  ⟨(fun x ↦ op (F.map x) (G.map x)), F.domain ∩ G.domain⟩

/-- ### 函数复合
    ### Functions Composition -/
def Function_comp (F G : Function) : Function :=
  ⟨(fun x ↦ F.map (G.map x)), F.domain ∩ G.domain⟩

instance : Add Function where
  add := (Function_op₂ · · (· + ·))
instance : Sub Function where
  sub := (Function_op₂ · · (· - ·))
instance : Mul Function where
  mul := (Function_op₂ · · (· * ·))
noncomputable instance : Div Function where
  div := (Function_op₂ · · (· / ·))
noncomputable instance : HomogeneousPow Function where
  pow := (Function_op₂ · · (· ^ ·))

infixr:90 " ⊙ " => (Function_comp · ·)
