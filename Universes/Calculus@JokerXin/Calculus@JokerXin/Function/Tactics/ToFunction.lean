import «Calculus@JokerXin».Function.Defs


/- ## Preparations -/

private lemma rewrite_Power {a : ℝ} (x : ℝ)
  : x^a = (Power a).map x
:= rfl
private lemma rewrite_Sqrt (x : ℝ)
  : √x = Sqrt.map x
:= rfl
private lemma rewrite_Abs (x : ℝ)
  : abs x = Abs.map x
:= rfl
private lemma rewrite_Exp (x : ℝ)
  : exp x = Exp.map x
:= rfl
private lemma rewrite_Ln (x : ℝ)
  : log x = Ln.map x
:= rfl
private lemma rewrite_Sin (x : ℝ)
  : sin x = Sin.map x
:= rfl
private lemma rewrite_Cos (x : ℝ)
  : cos x = Cos.map x
:= rfl
private lemma rewrite_Tan (x : ℝ)
  : tan x = Tan.map x
:= rfl
private lemma rewrite_Cot (x : ℝ)
  : cot x = Cot.map x
:= rfl
private lemma rewrite_Sinh (x : ℝ)
  : sinh x = Sinh.map x
:= rfl
private lemma rewrite_Cosh (x : ℝ)
  : cosh x = Cosh.map x
:= rfl
private lemma rewrite_Tanh (x : ℝ)
  : tanh x = Tanh.map x
:= rfl
private lemma rewrite_Arcsin (x : ℝ)
  : arcsin x = Arcsin.map x
:= rfl
private lemma rewrite_Arccos (x : ℝ)
  : arccos x = Arccos.map x
:= rfl
private lemma combine_Add {F G : Function} (x : ℝ)
  : F.map x + G.map x = (F + G).map x
:= rfl
private lemma combine_Sub {F G : Function} (x : ℝ)
  : F.map x - G.map x = (F - G).map x
:= rfl
private lemma combine_Mul {F G : Function} (x : ℝ)
  : F.map x * G.map x = (F * G).map x
:= rfl
private lemma combine_Div {F G : Function} (x : ℝ)
  : F.map x / G.map x = (F / G).map x
:= rfl
private lemma combine_Pow {F G : Function} (x : ℝ)
  : F.map x ^ G.map x = (F ^ G).map x
:= rfl


/- ## Tactics -/

/--
  ### Rewrite Lambda Expression to `Function`
  __Usage__ `to_Function`
-/
macro "to_Function" x₀:ident : tactic => `(tactic|
  try simp only [
    rewrite_Power $x₀,
    rewrite_Sqrt $x₀,
    rewrite_Abs $x₀,
    rewrite_Exp $x₀,
    rewrite_Ln $x₀,
    rewrite_Sin $x₀,
    rewrite_Cos $x₀,
    rewrite_Tan $x₀,
    rewrite_Cot $x₀,
    rewrite_Sinh $x₀,
    rewrite_Cosh $x₀,
    rewrite_Tanh $x₀,
    rewrite_Arcsin $x₀,
    rewrite_Arccos $x₀,
    combine_Add $x₀,
    combine_Sub $x₀,
    combine_Mul $x₀,
    combine_Div $x₀,
    combine_Pow $x₀
  ]
)
