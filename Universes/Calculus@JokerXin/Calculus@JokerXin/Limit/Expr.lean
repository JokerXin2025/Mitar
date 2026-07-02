import «Calculus@JokerXin».Limit.Defs
import «Calculus@JokerXin».Expr.UndeterminedEqual


/- ## 极限表达式 Limit Expression -/

noncomputable section

open Classical in
/-- ### 数列极限表达式
    ### Sequence Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℕ)\\to\\infty}@1" Expr]
def SeqLimitExpr (a : Sequence) : Option ℝ :=
  if h : SeqConvergesAt a then
    the (choose h)
  else none

open Classical in
/-- ### 函数极限表达式
    ### Function Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2}@1" Expr]
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : FuncConvergesAt ⟨f, Iii⟩ x₀ then
    the (choose h)
  else none

open Classical in
/-- ### 左极限表达式
    ### Left Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^-}@1" Expr]
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : LeftConvergesAt ⟨f, Iio x₀⟩ x₀ then
    the (choose h)
  else none

open Classical in
/-- ### 右极限表达式
    ### Right Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^+}@1" Expr]
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : RightConvergesAt ⟨f, Ioi x₀⟩ x₀ then
    the (choose h)
  else none

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)

end


/- ## 极限表达式的性质 Properties of Limit Expression -/

/-- ### 函数极限的局部同余性（表达式） -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : lim f x₀ =? lim g x₀
:= sorry

/-- ### 左极限的局部同余性（表达式） -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ =? lim₋ g x₀
:= sorry

/-- ### 右极限的局部同余性（表达式） -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ =? lim₊ g x₀
:= sorry

/-- ### 单位分式函数极限表达式
    ### Equal-to-one-fractional Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma FuncLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式左极限表达式
    ### Equal-to-one-fractional Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma LeftLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₋ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式右极限表达式
    ### Equal-to-one-fractional Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitBasic])]
lemma RightLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₊ (fun x ↦ f x / f x) x₀ = the 1
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


/- ## 极限 & 极限表达式 Limit & Limit Expression -/

open Classical in
/-- ### 函数极限表达式 → 函数极限
    ### Function Limit Expression → Function Limit -/
theorem FuncLimitExpr_to_FuncLimit {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Nbhd x₀ δ ⊆ I)
    (h_lim : FuncLimitExpr f x₀ = the A)
  : FuncLimit ⟨f, I⟩ x₀ A
:= by
  unfold FuncLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- ### 函数极限 → 函数极限表达式
    ### Function Limit → Function Limit Expression -/
theorem FuncLimit_to_FuncLimitExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_lim : FuncLimit ⟨f, I⟩ x₀ A)
  : FuncLimitExpr f x₀ = the A
:= by
  have h_lim_Iii : FuncLimit ⟨f, Iii⟩ x₀ A := by
    obtain ⟨⟨δ, hδ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, hδ_pos, fun x _ => trivial⟩, h_eps_delta⟩
  unfold FuncLimitExpr
  have h_conv : FuncConvergesAt ⟨f, Iii⟩ x₀ := ⟨A, h_lim_Iii⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact FuncLimit_Unique (choose_spec h_conv) h_lim_Iii

open Classical in
/-- ### 左极限表达式 → 左极限
    ### Left Limit Expression → Left Limit -/
theorem LeftLimitExpr_to_LeftLimit {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo (x₀ - δ) x₀ ⊆ I)
    (h_lim : lim₋ f x₀ = the A)
  : LeftLimit ⟨f, I⟩ x₀ A
:= by
  unfold LeftLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- ### 左极限 → 左极限表达式
    ### Left Limit → Left Limit Expression -/
theorem LeftLimit_to_LeftLimitExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_lim : LeftLimit ⟨f, I⟩ x₀ A)
  : lim₋ f x₀ = the A
:= by
  have h_lim_Iio : LeftLimit ⟨f, Iio x₀⟩ x₀ A := by
    obtain ⟨⟨δ, hδ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, hδ_pos, fun x hx => hx.2⟩, h_eps_delta⟩
  unfold LeftLimitExpr
  have h_conv : LeftConvergesAt ⟨f, Iio x₀⟩ x₀ := ⟨A, h_lim_Iio⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact LeftLimit_Unique (choose_spec h_conv) h_lim_Iio

open Classical in
/-- ### 右极限表达式 → 右极限
    ### Right Limit Expression → Right Limit -/
theorem RightLimitExpr_to_RightLimit {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_I : ∃ δ > 0, Ioo x₀ (x₀ + δ) ⊆ I)
    (h_lim : lim₊ f x₀ = the A)
  : RightLimit ⟨f, I⟩ x₀ A
:= by
  unfold RightLimitExpr at h_lim
  split at h_lim
  · rename_i h_conv
    injection h_lim with h_val_eq
    rw [← h_val_eq]
    exact ⟨h_I, (choose_spec h_conv).2⟩
  · contradiction

open Classical in
/-- ### 右极限 → 右极限表达式
    ### Right Limit → Right Limit Expression -/
theorem RightLimit_to_RightLimitExpr {f : ℝ → ℝ} {x₀ A : ℝ} {I : Set ℝ}
    (h_lim : RightLimit ⟨f, I⟩ x₀ A)
  : lim₊ f x₀ = the A
:= by
  have h_lim_Ioi : RightLimit ⟨f, Ioi x₀⟩ x₀ A := by
    obtain ⟨⟨δ, hδ_pos, _⟩, h_eps_delta⟩ := h_lim
    exact ⟨⟨δ, hδ_pos, fun x hx => hx.1⟩, h_eps_delta⟩
  unfold RightLimitExpr
  have h_conv : RightConvergesAt ⟨f, Ioi x₀⟩ x₀ := ⟨A, h_lim_Ioi⟩
  simp only [dif_pos h_conv]
  apply congrArg the
  exact RightLimit_Unique (choose_spec h_conv) h_lim_Ioi
