import «Calculus@JokerXin».Prelude


/- ## 数列的定义 Definition of Sequence -/

/-- ### 数列
    ### Sequence
    A Real number sequence with domain
    - `a.map`, `a.init` and `a.final` refer to `a`'s total map, initial item's
    index and the final item's index + 1, respectively -/
structure Sequence where
  map : ℕ → ℝ
  init : ℕ
  final : WithTop ℕ


/- ## 数列运算的定义 Definitions of Sequence Operations -/

/-- ### 自由一元运算
    ### Free Unary Operation -/
def Sequence_Free₁ (A : Sequence) (op₁ : ℝ → ℝ) : Sequence :=
  ⟨(fun x ↦ op₁ (A.map x)), A.init, A.final⟩

/-- ### 自由二元运算
    ### Free Binary Operation -/
def Sequence_Free₂ (A B : Sequence) (op₂ : ℝ → ℝ → ℝ) : Sequence :=
  ⟨(fun x ↦ op₂ (A.map x) (B.map x)), max A.init B.init, min A.final B.final⟩

/-- ### 数乘
    ### Scalar Multiplication -/
def Sequence_SMul (k : ℝ) (A : Sequence) : Sequence :=
  ⟨k • A.map, A.init, A.final⟩

/-- ### 乘法幂
    ### Multiplication Power -/
def Sequence_MPow (A : Sequence) (n : ℕ) : Sequence :=
  ⟨(fun x ↦ (A.map x)^n), A.init, A.final⟩

/- # To be Modified ↓ -/
/-
/-- ### 子列
    ### Subsequence -/
def Sequence_Sub (A : Sequence) : Sequence :=
  ⟨(fun x ↦ A.map (B.map x)), A.domain ∩ B.domain⟩
-/

instance : Add Sequence where
  add := (Sequence_Free₂ · · (· + ·))
instance : Sub Sequence where
  sub := (Sequence_Free₂ · · (· - ·))
instance : Mul Sequence where
  mul := (Sequence_Free₂ · · (· * ·))
noncomputable instance : Div Sequence where
  div a b := ⟨
    (fun x ↦ a.map x / b.map x),
    max a.init b.init,
    min (min a.final b.final) (some (sInf { n : ℕ | b.map n = 0 }))
  ⟩
/- # To be Modified ↓ -/
noncomputable instance : HomogeneousPow Sequence where
  pow := (Sequence_Free₂ · · (· ^ ·))
instance : SMul ℝ Sequence where
  smul := Sequence_SMul
instance : NatPow Sequence where
  pow := Sequence_MPow

-- infixr:90 " ⊙ " => (Sequence_Sub · ·)
