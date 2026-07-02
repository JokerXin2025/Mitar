import «Calculus@JokerXin».Sequence.Defs
import «Calculus@JokerXin».Function.Defs
import «Calculus@JokerXin».Function.Misc


/- ## 极限的定义 Definitions of Limit -/

/-- ### 数列极限
    ### Sequence Limit -/
@[Lean2TeX "数列@1收敛于@2" Text]
def SeqLimit (a : Sequence) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, a n ∈ Nbho L ε

/-- ### 数列收敛
    ### Sequence Converges -/
abbrev SeqConvergesAt (a : Sequence) : Prop :=
  ∃ L : ℝ, SeqLimit a L

/-- ### 函数极限
    ### Function Limit -/
@[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处收敛于@3" Text]
def FuncLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Nbhd x₀ δ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Nbhd x₀ δ, F.map x ∈ Nbho L ε)

/-- ### 函数收敛
    ### Function Converges -/
abbrev FuncConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, FuncLimit F x₀ L

/-- ### 左极限
    ### Left Limit -/
@[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处的左极限为@3" Text]
def LeftLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x ∈ Nbho L ε)

/-- ### 左收敛
    ### Left Converges -/
abbrev LeftConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, LeftLimit F x₀ L

/-- ### 右极限
    ### Right Limit -/
@[Lean2TeX "函数@1在 $#1(ℝ)=@2$ 处的右极限为@3" Text]
def RightLimit (F : Function) (x₀ L : ℝ) : Prop :=
  (∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ δ > 0,
      ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x ∈ Nbho L ε)

/-- ### 右收敛
    ### Right Converges -/
abbrev RightConvergesAt (F : Function) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, RightLimit F x₀ L


/- ## 极限的性质 Properties of Limit -/

/-- ### 数列极限的唯一性
    ### Sequence Limit's Uniqueness -/
theorem SeqLimit_Unique {a : Sequence} {A B : ℝ}
    (hA : SeqLimit a A) (hB : SeqLimit a B)
  : A = B
:= sorry

/-- ### 数列极限的保号性（正）
    ### Sequence Limit's Sign-Preservation (positive) -/
theorem SeqLimit_Preserve_pos {a : Sequence} {A : ℝ}
    (h_lim : SeqLimit a A) (h_A_pos : A > 0)
  : ∃ N : ℕ, ∀ n > N, a n > 0
:= sorry

/-- ### 数列极限的保号性（负）
    ### Sequence Limit's Sign-Preservation (negative) -/
theorem SeqLimit_Preserve_neg {a : Sequence} {A : ℝ}
    (h_lim : SeqLimit a A) (h_A_neg : A < 0)
  : ∃ N : ℕ, ∀ n > N, a n < 0
:= sorry

/-- ### 收敛数列的有界性
    ### Convergent Sequence's Boundedness -/
theorem ConvergentSeq_Bounded {a : Sequence}
    (h : ∃ L : ℝ, SeqLimit a L)
  : SeqBounded a
:= sorry

/-- ### 函数极限的唯一性
    ### Function Limit's Uniqueness -/
theorem FuncLimit_Unique {F : Function} {x₀ A B : ℝ}
    (hA : FuncLimit F x₀ A) (hB : FuncLimit F x₀ B)
  : A = B
:= sorry

/-- ### 函数极限的保号性（正）
    ### Function Limit's Sign-Preservation (positive) -/
theorem FuncLimit_Preserve_pos {F : Function} {x₀ A : ℝ}
    (h_lim : FuncLimit F x₀ A) (h_A_pos : A > 0)
  : ∃ δ > 0, ∀ x, |x - x₀| ∈ Ioo 0 δ → F.map x > 0
:= sorry

/-- ### 函数极限的保号性（负）
    ### Function Limit's Sign-Preservation (negative) -/
theorem FuncLimit_Preserve_neg {F : Function} {x₀ A : ℝ}
    (h_lim : FuncLimit F x₀ A) (h_A_neg : A < 0)
  : ∃ δ > 0, ∀ x, |x - x₀| ∈ Ioo 0 δ → F.map x < 0
:= sorry
/-
/-- ### 收敛函数的局部有界性
    ### Convergent Function's Local Boundedness -/
theorem ConvergentFunc_LocalBounded {F : Function} {x₀ : ℝ}
    (h : ∃ L : ℝ, FuncLimit F x₀ L)
  : FuncLocalBounded F x₀
:= sorry
-/
/-- ### 左极限的唯一性
    ### Left Limit's Uniqueness -/
theorem LeftLimit_Unique {F : Function} {x₀ A B : ℝ}
    (hA : LeftLimit F x₀ A) (hB : LeftLimit F x₀ B)
  : A = B
:= sorry

/-- ### 左极限的保号性（正）
    ### Left Limit's Sign-Preservation (positive) -/
theorem LeftLimit_Preserve_pos {F : Function} {x₀ A : ℝ}
    (h_lim : LeftLimit F x₀ A) (h_A_pos : A > 0)
  : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x > 0
:= sorry

/-- ### 左极限的保号性（负）
    ### Left Limit's Sign-Preservation (negative) -/
theorem LeftLimit_Preserve_neg {F : Function} {x₀ A : ℝ}
    (h_lim : LeftLimit F x₀ A) (h_A_neg : A < 0)
  : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x < 0
:= sorry

/-- ### 右极限的唯一性
    ### Right Limit's Uniqueness -/
theorem RightLimit_Unique {F : Function} {x₀ A B : ℝ}
    (hA : RightLimit F x₀ A) (hB : RightLimit F x₀ B)
  : A = B
:= sorry

/-- ### 右极限的保号性（正）
    ### Right Limit's Sign-Preservation (positive) -/
theorem RightLimit_Preserve_pos {F : Function} {x₀ A : ℝ}
    (h_lim : RightLimit F x₀ A) (h_A_pos : A > 0)
  : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x > 0
:= sorry

/-- ### 右极限的保号性（负）
    ### Right Limit's Sign-Preservation (negative) -/
theorem RightLimit_Preserve_neg {F : Function} {x₀ A : ℝ}
    (h_lim : RightLimit F x₀ A) (h_A_neg : A < 0)
  : ∃ δ > 0, ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x < 0
:= sorry

/-- ### 函数极限的邻域同余性 -/
lemma FuncLimit.Congr {F G : Function} {x₀ δ L : ℝ}
    (h_F : FuncLimit F x₀ L)
    (h : ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimit G x₀ L
:= sorry

/-- ### 左极限的邻域同余性 -/
lemma LeftLimit.Congr {F G : Function} {x₀ δ L : ℝ}
    (h_F : LeftLimit F x₀ L)
    (h : ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimit G x₀ L
:= sorry

/-- ### 右极限的邻域同余性 -/
lemma RightLimit.Congr {F G : Function} {x₀ δ L : ℝ}
    (h_F : RightLimit F x₀ L)
    (h : ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimit G x₀ L
:= sorry
