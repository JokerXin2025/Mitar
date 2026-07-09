import «Calculus@JokerXin».Limit.Defs
import «Calculus@JokerXin».Expr.Defs


/- ## 极限表达式 Limit Expression -/

noncomputable section

open Classical in
/-- ### 数列极限表达式
    ### Sequence Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℕ)\\to\\infty}@1" Expr]
def SeqLimitExpr (a : ℕ → Option ℝ) : Option ℝ :=
  if ∀ n, (a n).isSome then
    let a!! := fun n ↦ (a n).getD 0
    if h : SeqConvergesAt ⟨a!!, 0, none⟩ then
      the (choose h)
    else none
  else none

open Classical in
/-- ### 函数极限表达式
    ### Function Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2}@1" Expr]
def FuncLimitExpr (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : FuncConvergesAt ⟨f!!, Iii⟩ x₀ then
      the (choose h)
    else none
  else none

open Classical in
/-- ### 左极限表达式
    ### Left Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^-}@1" Expr]
def LeftLimitExpr (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : LeftConvergesAt ⟨f!!, Iii⟩ x₀ then
      the (choose h)
    else none
  else none

open Classical in
/-- ### 右极限表达式
    ### Right Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^+}@1" Expr]
def RightLimitExpr (f : ℝ → Option ℝ) (x₀ : ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : RightConvergesAt ⟨f!!, Iii⟩ x₀ then
      the (choose h)
    else none
  else none

open Classical in
/-- ### 负无穷处极限表达式
    ### Expression of Limit at Negative Infinity -/
def NegInftyLimitExpr (f : ℝ → Option ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : ConvergesAtNegInfty ⟨f!!, Iii⟩ then
      the (choose h)
    else none
  else none

open Classical in
/-- ### 正无穷处极限表达式
    ### Expression of Limit at Positive Infinity -/
def PosInftyLimitExpr (f : ℝ → Option ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : ConvergesAtPosInfty ⟨f!!, Iii⟩ then
      the (choose h)
    else none
  else none

open Classical in
/-- ### 无穷远处极限表达式
    ### Expression of Limit at Infinity -/
def InftyLimitExpr (f : ℝ → Option ℝ) : Option ℝ :=
  if ∀ x, (f x).isSome then
    let f!! := fun x ↦ (f x).getD 0
    if h : ConvergesAtInfty ⟨f!!, Iii⟩ then
      the (choose h)
    else none
  else none

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)
macro "lim₋∞" : term => `(NegInftyLimitExpr)
macro "lim₊∞" : term => `(PosInftyLimitExpr)
macro "lim∞" : term => `(InftyLimitExpr)

end


/- ## 极限表达式的性质 Properties of Limit Expression -/

/-
/-- ### 数列极限的局部同余性（表达式） -/
lemma SeqLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h_δ_pos : δ > 0)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : lim f x₀ =? lim g x₀
:= sorry
-/

/-- ### 函数极限的局部同余性（表达式） -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h_δ_pos : δ > 0)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : lim f x₀ =? lim g x₀
:= sorry

/-- ### 左极限的局部同余性（表达式） -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h_δ_pos : δ > 0)
    (h : ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ =? lim₋ g x₀
:= sorry

/-- ### 右极限的局部同余性（表达式） -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h_δ_pos : δ > 0)
    (h : ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ =? lim₊ g x₀
:= sorry

/-- ### 负无穷处极限的局部同余性（表达式） -/
lemma NegInftyLimitExpr.Congr {f g : ℝ → ℝ} (M : ℝ)
    (h_M_pos : M > 0)
    (h : ∀ x ∈ Iio (-M), f x = g x)
  : lim₋∞ f =? lim₋∞ g
:= sorry

/-- ### 正无穷处极限的局部同余性（表达式） -/
lemma PosInftyLimitExpr.Congr {f g : ℝ → ℝ} (M : ℝ)
    (h_M_pos : M > 0)
    (h : ∀ x ∈ Ioi M, f x = g x)
  : lim₊∞ f =? lim₊∞ g
:= sorry

/-- ### 无穷远处极限的局部同余性（表达式） -/
lemma InftyLimitExpr.Congr {f g : ℝ → ℝ} (M : ℝ)
    (h_M_pos : M > 0)
    (h : ∀ x ∈ Iio (-M), f x = g x
         ∧ ∀ x ∈ Ioi M, f x = g x)
  : lim∞ f =? lim∞ g
:= sorry

/- # To be Modified ↓ -/
/-
/-- ### 单位分式的函数极限表达式 !!!!!
    ### Equal-to-one-fractional Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式的左极限表达式 !!!!!
    ### Equal-to-one-fractional Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₋ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式的右极限表达式 !!!!!
    ### Equal-to-one-fractional Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma RightLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₊ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式的负无穷处极限表达式 !!!!!
    ### Equal-to-one-fractional Expression of Limit at Negative Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma NegInftyLimitExpr.DivSelf {f : ℝ → ℝ}
  : lim₋∞ (fun x ↦ f x / f x) = the 1
:= sorry

/-- ### 单位分式的正无穷处极限表达式 !!!!!
    ### Equal-to-one-fractional Expression of Limit at Positive Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma PosInftyLimitExpr.DivSelf {f : ℝ → ℝ}
  : lim₊∞ (fun x ↦ f x / f x) = the 1
:= sorry

/-- ### 单位分式的无穷远处极限表达式 !!!!!
    ### Equal-to-one-fractional Expression of Limit at Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma InftyLimitExpr.DivSelf {f : ℝ → ℝ}
  : lim∞ (fun x ↦ f x / f x) = the 1
:= sorry

/-- ### 函数极限表达式的强制左约分
    ### Forced Left Reduction of Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim ((f * g) / (f * g')) x₀ = lim (g / g') x₀
:= sorry

/-- ### 函数极限表达式的强制右约分
    ### Forced Right Reduction of Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim ((f * g) / (f' * g)) x₀ = lim (f / f') x₀
:= sorry

/-- ### 左极限表达式的强制左约分
    ### Forced Left Reduction of Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim₋ ((f * g) / (f * g')) x₀ = lim₋ (g / g') x₀
:= sorry

/-- ### 左极限表达式的强制右约分
    ### Forced Right Reduction of Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim₋ ((f * g) / (f' * g)) x₀ = lim₋ (f / f') x₀
:= sorry

/-- ### 右极限表达式的强制左约分
    ### Forced Left Reduction of Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim₊ ((f * g) / (f * g')) x₀ = lim₊ (g / g') x₀
:= sorry

/-- ### 右极限表达式的强制右约分
    ### Forced Right Reduction of Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma RightLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim₊ ((f * g) / (f' * g)) x₀ = lim₊ (f / f') x₀
:= sorry

/-- ### 负无穷处极限表达式的强制左约分
    ### Forced Left Reduction of Expression of Limit at Negative Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma NegInftyLimitExpr.Reduce {f g g' : ℝ → ℝ}
  : lim₋∞ ((f * g) / (f * g')) = lim₋∞ (g / g')
:= sorry

/-- ### 负无穷处极限表达式的强制右约分
    ### Forced Right Reduction of Expression of Limit at Negative Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma NegInftyLimitExpr.Reduce' {f f' g : ℝ → ℝ}
  : lim₋∞ ((f * g) / (f' * g)) = lim₋∞ (f / f')
:= sorry

/-- ### 正无穷处极限表达式的强制左约分
    ### Forced Left Reduction of Expression of Limit at Positive Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma PosInftyLimitExpr.Reduce {f g g' : ℝ → ℝ}
  : lim₊∞ ((f * g) / (f * g')) = lim₊∞ (g / g')
:= sorry

/-- ### 正无穷处极限表达式的强制右约分
    ### Forced Right Reduction of Expression of Limit at Positive Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma PosInftyLimitExpr.Reduce' {f f' g : ℝ → ℝ}
  : lim₊∞ ((f * g) / (f' * g)) = lim₊∞ (f / f')
:= sorry

/-- ### 无穷远处极限表达式的强制左约分
    ### Forced Left Reduction of Expression of Limit at Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma InftyLimitExpr.Reduce {f g g' : ℝ → ℝ}
  : lim∞ ((f * g) / (f * g')) = lim∞ (g / g')
:= sorry

/-- ### 无穷远处极限表达式的强制右约分
    ### Forced Right Reduction of Expression of Limit at Infinity -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma InftyLimitExpr.Reduce' {f f' g : ℝ → ℝ}
  : lim∞ ((f * g) / (f' * g)) = lim∞ (f / f')
:= sorry
-/


/- ## 极限 & 极限表达式 Limit & Limit Expression -/

open Classical in
/-- ### 函数极限表达式 → 函数极限
    ### Function Limit Expression → Function Limit -/
theorem FuncLimitExpr_to_FuncLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_lim : FuncLimitExpr f x₀ = the L)
  : FuncLimit ⟨f, I⟩ x₀ L
:= sorry/-by
  unfold FuncLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction-/

open Classical in
/-- ### 函数极限 → 函数极限表达式
    ### Function Limit → Function Limit Expression -/
theorem FuncLimit_to_FuncLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : FuncLimit ⟨f, I⟩ x₀ L)
  : FuncLimitExpr f x₀ = the L
:= sorry/-by
  have h_lim_Iii : FuncLimit ⟨f, Iii⟩ x₀ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold FuncLimitExpr
  have h_conv : FuncConvergesAt ⟨f, Iii⟩ x₀ := ⟨L, h_lim_Iii⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact FuncLimit_Unique (choose_spec h_conv) h_lim_Iii-/

open Classical in
/-- ### 左极限表达式 → 左极限
    ### Left Limit Expression → Left Limit -/
theorem LeftLimitExpr_to_LeftLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ I)
    (h_lim : lim₋ f x₀ = the L)
  : LeftLimit ⟨f, I⟩ x₀ L
:= sorry/-by
  unfold LeftLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction-/

open Classical in
/-- ### 左极限 → 左极限表达式
    ### Left Limit → Left Limit Expression -/
theorem LeftLimit_to_LeftLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : LeftLimit ⟨f, I⟩ x₀ L)
  : lim₋ f x₀ = the L
:= sorry/-by
  have h_lim : LeftLimit ⟨f, Iii⟩ x₀ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold LeftLimitExpr
  have h_conv : LeftConvergesAt ⟨f, Iii⟩ x₀ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact LeftLimit_Unique (choose_spec h_conv) h_lim-/

open Classical in
/-- ### 右极限表达式 → 右极限
    ### Right Limit Expression → Right Limit -/
theorem RightLimitExpr_to_RightLimit {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ I)
    (h_lim : lim₊ f x₀ = the L)
  : RightLimit ⟨f, I⟩ x₀ L
:= sorry/-by
  unfold RightLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction-/

open Classical in
/-- ### 右极限 → 右极限表达式
    ### Right Limit → Right Limit Expression -/
theorem RightLimit_to_RightLimitExpr {f : ℝ → ℝ} {x₀ L : ℝ} {I : Set ℝ}
    (h_lim : RightLimit ⟨f, I⟩ x₀ L)
  : lim₊ f x₀ = the L
:= sorry/-by
  have h_lim : RightLimit ⟨f, Iii⟩ x₀ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold RightLimitExpr
  have h_conv : RightConvergesAt ⟨f, Iii⟩ x₀ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact RightLimit_Unique (choose_spec h_conv) h_lim-/

open Classical in
/-- ### 负无穷处极限表达式 → 负无穷处极限
    ### Expression of Limit at Negative Infinity → Limit at Negative Infinity -/
theorem NegInftyLimitExpr_to_NegInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Iio (-M) ⊆ I)
    (h_lim : lim₋∞ f = the L)
  : NegInftyLimit ⟨f, I⟩ L
:= sorry/-by
  unfold NegInftyLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction-/

open Classical in
/-- ### 负无穷处极限 → 负无穷处极限表达式
    ### Limit at Negative Infinity → Expression of Limit at Negative Infinity -/
theorem NegInftyLimit_to_NegInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : NegInftyLimit ⟨f, I⟩ L)
  : lim₋∞ f = the L
:= sorry/-by
  have h_lim : NegInftyLimit ⟨f, Iii⟩ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold NegInftyLimitExpr
  have h_conv : ConvergesAtNegInfty ⟨f, Iii⟩ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact NegInftyLimit_Unique (choose_spec h_conv) h_lim-/

open Classical in
/-- ### 正无穷处极限表达式 → 正无穷处极限
    ### Expression of Limit at Positive Infinity → Limit at Positive Infinity -/
theorem PosInftyLimitExpr_to_PosInftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : ∃ M > 0, Ioi M ⊆ I)
    (h_lim : lim₊∞ f = the L)
  : PosInftyLimit ⟨f, I⟩ L
:= sorry/-by
  unfold PosInftyLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction-/

open Classical in
/-- ### 正无穷处极限 → 正无穷处极限表达式
    ### Limit at Positive Infinity → Expression of Limit at Positive Infinity -/
theorem PosInftyLimit_to_PosInftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : PosInftyLimit ⟨f, I⟩ L)
  : lim₊∞ f = the L
:= sorry/-by
  have h_lim : PosInftyLimit ⟨f, Iii⟩ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold PosInftyLimitExpr
  have h_conv : ConvergesAtPosInfty ⟨f, Iii⟩ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact PosInftyLimit_Unique (choose_spec h_conv) h_lim-/

/- # To be Modified ↓ -/
/-
open Classical in
/-- ### 无穷远处极限表达式 → 无穷远处极限
    ### Expression of Limit at Infinity → Limit at Infinity -/
theorem InftyLimitExpr_to_InftyLimit {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_I : Iio (-M) ⊆ I ∧ Ioi M ⊆ I)
    (h_lim : lim∞ f = the L)
  : InftyLimit ⟨f, I⟩ L
:= by
  unfold InftyLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- ### 无穷远处极限 → 无穷远处极限表达式
    ### Limit at Infinity → Expression of Limit at Infinity -/
theorem InftyLimit_to_InftyLimitExpr {f : ℝ → ℝ} {L : ℝ} {I : Set ℝ}
    (h_lim : PosInftyLimit ⟨f, I⟩ L)
  : lim∞ f = the L
:= by
  have h_lim : InftyLimit ⟨f, Iii⟩ L := by
    obtain ⟨⟨δ, h_δ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, h_δ_pos, fun x _ _ => trivial⟩, h_eps_delta⟩
  unfold InftyLimitExpr
  have h_conv : ConvergesAtInfty ⟨f, Iii⟩ := ⟨L, h_lim⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact InftyLimit_Unique (choose_spec h_conv) h_lim
-/

/-- ### 函数极限 → 左极限（表达式）
    ### Function Limit → Left Limit (Expression) -/
theorem FuncLimitExpr.toLeft {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₋ f x₀ =? lim f x₀
:= sorry

/-- ### 函数极限 → 右极限（表达式）
    ### Function Limit → Right Limit (Expression) -/
theorem FuncLimitExpr.toRight {f : ℝ → ℝ} {x₀ : ℝ}
  : lim₊ f x₀ =? lim f x₀
:= sorry

/-- ### 无穷远处极限 → 负无穷处极限（表达式）
    ### Limit at Infinity → Limit at Negative Infinity (Expression) -/
theorem InftyLimitExpr.toNeg {f : ℝ → ℝ}
  : lim₋∞ f =? lim∞ f
:= sorry

/-- ### 无穷远处极限 → 正无穷处极限（表达式）
    ### Limit at Infinity → Limit at Positive Infinity (Expression) -/
theorem InftyLimitExpr.toPos {f : ℝ → ℝ}
  : lim₊∞ f =? lim∞ f
:= sorry
