import «Calculus@Mitar».Limit.Defs
import «Calculus@Mitar».Expr.UndeterminedEqual


/- All the limit conclusions related to calculations ought to be presented in the form
    of expressions. -/

/- ## 极限表达式 Limit Expression -/

noncomputable section

open Classical in
/-- ### 数列极限表达式
    ### Sequence Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℕ)\\to\\infty}@1" Expr]
def SeqLimitExpr (a : Sequence) : Option ℝ :=
  if h : SeqConverges a then
    the (choose h)
  else none

open Classical in
/-- ### 函数极限表达式
    ### Function Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2}@1" Expr]
def FuncLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : FuncConverges ⟨f, Iii⟩ x₀ then
    the (choose h)
  else none

open Classical in
/-- ### 左极限表达式
    ### Left Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^-}@1" Expr]
def LeftLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : LeftConverges ⟨f, Iio x₀⟩ x₀ then
    the (choose h)
  else none

open Classical in
/-- ### 右极限表达式
    ### Right Limit Expression -/
@[Lean2TeX "\\lim\\limits_{#1(ℝ)\\to@2^+}@1" Expr]
def RightLimitExpr (f : ℝ → ℝ) (x₀ : ℝ) : Option ℝ :=
  if h : RightConverges ⟨f, Ioi x₀⟩ x₀ then
    the (choose h)
  else none

macro "limₙ" : term => `(SeqLimitExpr)
macro "lim" : term => `(FuncLimitExpr)
macro "lim₋" : term => `(LeftLimitExpr)
macro "lim₊" : term => `(RightLimitExpr)

end

open Classical in
@[aesop safe apply (rule_sets := [InitializeExpr])]
theorem FuncLimitExpr_isFuncLimit {F : Function} {x₀ L : ℝ}
    (h_lim : lim F.map x₀ = the L)
  : FuncLimit F x₀ L
:= by
  unfold FuncLimitExpr at h_lim
  split at h_lim
  next h_conv =>
    injection h_lim with h_eq
    rw [← h_eq]
    exact choose_spec h_conv
  next h_not_conv =>
    contradiction

/-- ### 函数极限表达式的局部同余性
    ### Function Limit Expression's Local Congruence -/
lemma FuncLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), f x = g x)
  : lim f x₀ =? lim g x₀
:= sorry

/-- ### 左极限表达式的局部同余性
    ### Left Limit Expression's Local Congruence -/
lemma LeftLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo (x₀ - δ) x₀, f x = g x)
  : lim₋ f x₀ =? lim₋ g x₀
:= sorry

/-- ### 右极限表达式的局部同余性
    ### Right Limit Expression's Local Congruence -/
lemma RightLimitExpr.Congr {f g : ℝ → ℝ} {x₀ : ℝ} (δ : ℝ)
    (h : ∀ x ∈ Ioo x₀ (x₀ + δ), f x = g x)
  : lim₊ f x₀ =? lim₊ g x₀
:= sorry


/- ## 极限表达式的性质 Properties of Limit Expression -/

/-- ### 单位分式函数极限表达式
    ### Equal-to-one-fractional Function Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma FuncLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式左极限表达式
    ### Equal-to-one-fractional Left Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma LeftLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₋ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 单位分式右极限表达式
    ### Equal-to-one-fractional Right Limit Expression -/
@[aesop norm simp (rule_sets := [LimitSimplify])]
lemma RightLimitExpr.DivSelf {x₀ : ℝ} {f : ℝ → ℝ}
  : lim₊ (fun x ↦ f x / f x) x₀ = the 1
:= sorry

/-- ### 函数极限表达式的强制左约分
    ### Forced Left Reduction of Function Limit Expression -/
lemma FuncLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim ((f * g) / (f * g')) x₀ = lim (g / g') x₀
:= sorry

/-- ### 函数极限表达式的强制右约分
    ### Forced Right Reduction of Function Limit Expression -/
lemma FuncLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim ((f * g) / (f' * g)) x₀ = lim (f / f') x₀
:= sorry

/-- ### 左极限表达式的强制左约分
    ### Forced Left Reduction of Left Limit Expression -/
lemma LeftLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim₋ ((f * g) / (f * g')) x₀ = lim₋ (g / g') x₀
:= sorry

/-- ### 左极限表达式的强制右约分
    ### Forced Right Reduction of Left Limit Expression -/
lemma LeftLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim₋ ((f * g) / (f' * g)) x₀ = lim₋ (f / f') x₀
:= sorry

/-- ### 右极限表达式的强制左约分
    ### Forced Left Reduction of Right Limit Expression -/
lemma RightLimitExpr.Reduce {x₀ : ℝ} {f g g' : ℝ → ℝ}
  : lim₊ ((f * g) / (f * g')) x₀ = lim₊ (g / g') x₀
:= sorry

/-- ### 右极限表达式的强制右约分
    ### Forced Right Reduction of Right Limit Expression -/
lemma RightLimitExpr.Reduce' {x₀ : ℝ} {f f' g : ℝ → ℝ}
  : lim₊ ((f * g) / (f' * g)) x₀ = lim₊ (f / f') x₀
:= sorry
