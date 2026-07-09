import «Calculus@JokerXin».Sequence.Defs
import «Calculus@JokerXin».Sequence.Concept
import «Calculus@JokerXin».Function.Defs
import «Calculus@JokerXin».Function.Concept


/- ## 极限的定义 Definitions of Limit -/

/-- ### 数列极限
    ### Sequence Limit -/
@[Lean2TeX "数列@1收敛于@2" Text]
def SeqLimit (A : Sequence) (L : ℝ) : Prop :=
  A.final = none
  ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n > N, A.map n ∈ Nbho L ε

/-- ### 数列收敛
    ### Sequence Converges -/
abbrev SeqConvergesAt (A : Sequence) : Prop :=
  ∃ L : ℝ, SeqLimit A L

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

/-- ### 负无穷处极限
    ### Limit at Negative Infinity -/
def NegInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε)

/-- ### 在负无穷处收敛
    ### Converges at Negative Infinity -/
abbrev ConvergesAtNegInfty (F : Function) : Prop :=
  ∃ L : ℝ, NegInftyLimit F L

/-- ### 正无穷处极限
    ### Limit at Positive Infinity -/
def PosInftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Ioi M, F.map x ∈ Nbho L ε)

/-- ### 在正无穷处收敛
    ### Converges at Positive Infinity -/
abbrev ConvergesAtPosInfty (F : Function) : Prop :=
  ∃ L : ℝ, PosInftyLimit F L

/-- ### 无穷远处极限
    ### Limit at Infinity -/
def InftyLimit (F : Function) (L : ℝ) : Prop :=
  (∃ M > 0, Iio (-M) ⊆ F.domain ∧ Ioi M ⊆ F.domain)
  ∧ (∀ ε > 0, ∃ M > 0,
      ∀ x ∈ Iio (-M), F.map x ∈ Nbho L ε
      ∧ ∀ x ∈ Ioi M, F.map x ∈ Nbho L ε)

/-- ### 在无穷远处收敛
    ### Converges at Infinity -/
abbrev ConvergesAtInfty (F : Function) : Prop :=
  ∃ L : ℝ, InftyLimit F L


/- ## 极限的性质 Properties of Limit -/

/-- ### 数列极限的唯一性
    ### Uniqueness of Sequence Limit -/
theorem SeqLimit_Unique {A : Sequence} {L1 L2 : ℝ}
    (h1 : SeqLimit A L1) (h2 : SeqLimit A L2)
  : L1 = L2
:= sorry

/-- ### 收敛数列的有界性
    ### Boundedness of Convergent Sequence -/
theorem ConvergentSeq_Bounded {A : Sequence}
    (h : ∃ L : ℝ, SeqLimit A L)
  : SeqBounded A
:= sorry

/-- ### 函数极限的唯一性
    ### Uniqueness of Function Limit -/
theorem FuncLimit_Unique {F : Function} {x₀ L1 L2 : ℝ}
    (h1 : FuncLimit F x₀ L1) (h2 : FuncLimit F x₀ L2)
  : L1 = L2
:= sorry

/- # To be Modified ↓ -/
/-
/-- ### 收敛函数的局部有界性
    ### Local Boundedness of Convergent Function -/
theorem ConvergentFunc_LocalBounded {F : Function} {x₀ : ℝ}
    (h : ∃ L : ℝ, FuncLimit F x₀ L)
  : FuncLocalBounded F x₀
:= sorry
-/

/-- ### 左极限的唯一性
    ### Uniqueness of Left Limit -/
theorem LeftLimit_Unique {F : Function} {x₀ L1 L2 : ℝ}
    (h1 : LeftLimit F x₀ L1) (h2 : LeftLimit F x₀ L2)
  : L1 = L2
:= sorry

/-- ### 右极限的唯一性
    ### Uniqueness of Right Limit -/
theorem RightLimit_Unique {F : Function} {x₀ L1 L2 : ℝ}
    (h1 : RightLimit F x₀ L1) (h2 : RightLimit F x₀ L2)
  : L1 = L2
:= sorry

/-- ### 负无穷处极限的唯一性
    ### Uniqueness of Limit at Negative Infinity -/
theorem NegInftyLimit_Unique {F : Function} {L1 L2 : ℝ}
    (h1 : NegInftyLimit F L1) (h2 : NegInftyLimit F L2)
  : L1 = L2
:= sorry

/-- ### 正无穷处极限的唯一性
    ### Uniqueness of Limit at Positive Infinity -/
theorem PosInftyLimit_Unique {F : Function} {L1 L2 : ℝ}
    (h1 : PosInftyLimit F L1) (h2 : PosInftyLimit F L2)
  : L1 = L2
:= sorry

/-- ### 无穷远处极限的唯一性
    ### Uniqueness of Limit at Infinity -/
theorem InftyLimit_Unique {F : Function} {L1 L2 : ℝ}
    (h1 : InftyLimit F L1) (h2 : InftyLimit F L2)
  : L1 = L2
:= sorry

/-- ### 数列极限的邻域同余性 -/
lemma SeqLimit.Congr {A B : Sequence} {L : ℝ} {N : ℕ}
    (h_a : SeqLimit A L)
    (h : ∀ n > N, A.map n = B.map n)
  : SeqLimit B L
:= sorry

/-- ### 函数极限的邻域同余性 -/
lemma FuncLimit.Congr {F G : Function} {x₀ L δ : ℝ}
    (h_δ_pos : δ > 0)
    (h_F : FuncLimit F x₀ L)
    (h : ∀ x ∈ Nbhd x₀ δ, F.map x = G.map x)
  : FuncLimit G x₀ L
:= sorry

/-- ### 左极限的邻域同余性 -/
lemma LeftLimit.Congr {F G : Function} {x₀ L δ : ℝ}
    (h_δ_pos : δ > 0)
    (h_F : LeftLimit F x₀ L)
    (h : ∀ x ∈ Ioo (x₀ - δ) x₀, F.map x = G.map x)
  : LeftLimit G x₀ L
:= sorry

/-- ### 右极限的邻域同余性 -/
lemma RightLimit.Congr {F G : Function} {x₀ L δ : ℝ}
    (h_δ_pos : δ > 0)
    (h_F : RightLimit F x₀ L)
    (h : ∀ x ∈ Ioo x₀ (x₀ + δ), F.map x = G.map x)
  : RightLimit G x₀ L
:= sorry

/-- ### 负无穷处极限的邻域同余性 -/
lemma NegInftyLimit.Congr {F G : Function} {L M : ℝ}
    (h_M_pos : M > 0)
    (h_F : NegInftyLimit F L)
    (h : ∀ x ∈ Iio (-M), F.map x = G.map x)
  : NegInftyLimit G L
:= sorry

/-- ### 正无穷处极限的邻域同余性 -/
lemma PosInftyLimit.Congr {F G : Function} {L M : ℝ}
    (h_M_pos : M > 0)
    (h_F : PosInftyLimit F L)
    (h : ∀ x ∈ Ioi M, F.map x = G.map x)
  : PosInftyLimit G L
:= sorry

/-- ### 无穷远处极限的邻域同余性 -/
lemma InftyLimit.Congr {F G : Function} {L M : ℝ}
    (h_M_pos : M > 0)
    (h_F : InftyLimit F L)
    (h : ∀ x ∈ Iio (-M), F.map x = G.map x
         ∧ ∀ x ∈ Ioi M, F.map x = G.map x)
  : InftyLimit G L
:= sorry

/-- ### 函数极限 → 左极限
    ### Function Limit → Left Limit -/
theorem FuncLimit.toLeft {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : LeftLimit F x₀ L
:= sorry

/-- ### 函数极限 → 右极限
    ### Function Limit → Right Limit -/
theorem FuncLimit.toRight {F : Function} {x₀ L : ℝ}
    (h_lim : FuncLimit F x₀ L)
  : RightLimit F x₀ L
:= sorry

/-- ### 无穷远处极限 → 负无穷处极限
    ### Limit at Infinity → Limit at Negative Infinity -/
theorem InftyLimit.toNeg {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : NegInftyLimit F L
:= sorry

/-- ### 无穷远处极限 → 正无穷处极限
    ### Limit at Infinity → Limit at Positive Infinity -/
theorem InftyLimit.toPos {F : Function} {L : ℝ}
    (h_lim : InftyLimit F L)
  : PosInftyLimit F L
:= sorry

/-- ### 函数极限 → 数列极限
    ### Function Limit → Sequence Limit -/
theorem FuncLimit.toSeq {A : Sequence} {F : Function} {x₀ L : ℝ}
    (h_lim_F : FuncLimit F x₀ L)
    (h_lim_A : SeqLimit A x₀)
    (h_A_in_dom : ∀ n ≥ A.init, A.map n ∈ F.domain)
    (h_A_ne_x₀ : ∃ N : ℕ, ∀ n > N, A.map n ≠ x₀)
  : SeqLimit A L
:= sorry
