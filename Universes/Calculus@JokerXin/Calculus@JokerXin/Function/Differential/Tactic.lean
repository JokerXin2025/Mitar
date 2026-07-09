import «Calculus@JokerXin».Expr.Tactics
import «Calculus@JokerXin».Function.Differential.Elementary


/- ## Preparations -/

private class AutoDeriv (f : ℝ → ℝ) (x₀ : ℝ)
    (val : outParam ℝ) (cond : outParam Prop) where
  eq : cond → D f x₀ = the val

private instance deriv_patch₁ {k x₀ : ℝ}
  : AutoDeriv (fun x ↦ k + x) x₀ 1 True where
  eq := sorry

private instance deriv_patch₂ {k x₀ : ℝ}
  : AutoDeriv (fun x ↦ k - x) x₀ (-1) True where
  eq := sorry

private instance deriv_patch₃ {k x₀ : ℝ}
  : AutoDeriv (fun x ↦ k * x) x₀ k True where
  eq := sorry

private instance deriv_Constant {C x₀ : ℝ}
  : AutoDeriv (fun _ ↦ C) x₀ 0 True where
  eq := directly DerivExpr.Constant

private instance deriv_Identity {x₀ : ℝ}
  : AutoDeriv (·) x₀ 1 True where
  eq := directly DerivExpr.Identity

private instance deriv_SMul {f : ℝ → ℝ} {k x₀ D₁ : ℝ} {c₁ : Prop}
    [AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (k • f) x₀ (k * D₁) c₁ where
  eq := sorry

private instance deriv_Add {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f + g) x₀ (D₁ + D₂) (c₁ ∧ c₂) where
  eq := sorry

private instance deriv_Add' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x + g x) x₀ (D₁ + D₂) (c₁ ∧ c₂) where
  eq := sorry

private instance deriv_Sub {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f - g) x₀ (D₁ - D₂) (c₁ ∧ c₂) where
  eq := sorry

private instance deriv_Sub' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x - g x) x₀ (D₁ - D₂) (c₁ ∧ c₂) where
  eq := sorry

private instance deriv_Mul {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f * g) x₀ (D₁ * g x₀ + f x₀ * D₂) (c₁ ∧ c₂) where
  eq := sorry

private instance deriv_Mul' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x * g x) x₀ (D₁ * g x₀ + f x₀ * D₂) (c₁ ∧ c₂) where
  eq := sorry

private instance deriv_Div {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (f / g) x₀
    ((D₁ * g x₀ - f x₀ * D₂) / (g x₀)^2) (c₁ ∧ c₂ ∧ g x₀ ≠ 0) where
  eq := sorry

private instance deriv_Div' {f g : ℝ → ℝ} {x₀ D₁ D₂ : ℝ} {c₁ c₂ : Prop}
    [AutoDeriv f x₀ D₁ c₁] [AutoDeriv g x₀ D₂ c₂]
  : AutoDeriv (fun x ↦ f x / g x) x₀
    ((D₁ * g x₀ - f x₀ * D₂) / (g x₀)^2) (c₁ ∧ c₂ ∧ g x₀ ≠ 0) where
  eq := sorry

private instance deriv_Abs {x₀ : ℝ}
  : AutoDeriv (|·|) x₀ (x₀ / |x₀|) (x₀ ≠ 0) where
  eq := DerivExpr.Abs

private instance deriv_Sqrt {x₀ : ℝ}
  : AutoDeriv (√·) x₀ (1 / (2 * √x₀)) (x₀ > 0) where
  eq := DerivExpr.Sqrt

private instance deriv_Exp {x₀ : ℝ}
  : AutoDeriv exp x₀ (exp x₀) True where
  eq := directly DerivExpr.Exp

private instance deriv_Ln {x₀ : ℝ}
  : AutoDeriv ln x₀ (1 / x₀) (x₀ > 0) where
  eq := DerivExpr.Ln

private instance deriv_Sin {x₀ : ℝ}
  : AutoDeriv sin x₀ (cos x₀) True where
  eq := directly DerivExpr.Sin

private instance deriv_Cos {x₀ : ℝ}
  : AutoDeriv cos x₀ (- sin x₀) True where
  eq := directly DerivExpr.Cos

private instance deriv_Tan {x₀ : ℝ}
  : AutoDeriv tan x₀ (sec x₀ ^2) (cos x₀ ≠ 0) where
  eq := DerivExpr.Tan

private instance deriv_Cot {x₀ : ℝ}
  : AutoDeriv cot x₀ (- csc x₀ ^2) (sin x₀ ≠ 0) where
  eq := DerivExpr.Cot

private instance deriv_Sec {x₀ : ℝ}
  : AutoDeriv sec x₀ (tan x₀ * sec x₀) (cos x₀ ≠ 0) where
  eq := DerivExpr.Sec

private instance deriv_Csc {x₀ : ℝ}
  : AutoDeriv csc x₀ (- cot x₀ * csc x₀) (sin x₀ ≠ 0) where
  eq := DerivExpr.Csc

private instance deriv_Sinh {x₀ : ℝ}
  : AutoDeriv sinh x₀ (cosh x₀) True where
  eq := directly DerivExpr.Sinh

private instance deriv_Cosh {x₀ : ℝ}
  : AutoDeriv cosh x₀ (sinh x₀) True where
  eq := directly DerivExpr.Cosh

private instance deriv_Tanh {x₀ : ℝ}
  : AutoDeriv tanh x₀ (sech x₀ ^2) True where
  eq := directly DerivExpr.Tanh

private instance deriv_Coth {x₀ : ℝ}
  : AutoDeriv coth x₀ (- csch x₀ ^2) (x₀ ≠ 0) where
  eq := DerivExpr.Coth

private instance deriv_Sech {x₀ : ℝ}
  : AutoDeriv sech x₀ (- tanh x₀ * sech x₀) True where
  eq := directly DerivExpr.Sech

private instance deriv_Csch {x₀ : ℝ}
  : AutoDeriv csch x₀ (- coth x₀ * csch x₀) (x₀ ≠ 0) where
  eq := DerivExpr.Csch

private instance deriv_Arcsin {x₀ : ℝ}
  : AutoDeriv arcsin x₀ (1 / √(1 - x₀^2)) (x₀ > -1 ∧ x₀ < 1) where
  eq := DerivExpr.Arcsin

private instance deriv_Arccos {x₀ : ℝ}
  : AutoDeriv arccos x₀ (-1 / √(1 - x₀^2)) (x₀ > -1 ∧ x₀ < 1) where
  eq := DerivExpr.Arccos

private instance deriv_Arctan {x₀ : ℝ}
  : AutoDeriv arctan x₀ (1 / (1 + x₀^2)) True where
  eq := directly DerivExpr.Arctan

private instance deriv_Arccot {x₀ : ℝ}
  : AutoDeriv arccot x₀ (-1 / (1 + x₀^2)) True where
  eq := directly DerivExpr.Arccot

private instance deriv_Arcsec {x₀ : ℝ}
  : AutoDeriv arcsec x₀ (1 / (|x₀| * √(x₀^2 - 1))) (x₀ < -1 ∨ x₀ > 1) where
  eq := DerivExpr.Arcsec

private instance deriv_Arccsc {x₀ : ℝ}
  : AutoDeriv arccsc x₀ (-1 / (|x₀| * √(x₀^2 - 1))) (x₀ < -1 ∨ x₀ > 1) where
  eq := DerivExpr.Arccsc

private instance deriv_compAbs {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((|·|) ∘ f) x₀
    (f x₀ / |f x₀| * D₁) (c₁ ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_f_nonzero⟩
    have h_chain : D ((|·|) ∘ f) x₀ =? D (|·|) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Abs h_f_nonzero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compAbs' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ |f x|) x₀
    (f x₀ / |f x₀| * D₁) (c₁ ∧ f x₀ ≠ 0) where
  eq := deriv_compAbs.eq

private instance deriv_compSqrt {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv ((√·) ∘ f) x₀
    (1 / (2 * √(f x₀)) * D₁) (c₁ ∧ f x₀ > 0) where
  eq := by
    intro ⟨h_cond, h_f_pos⟩
    have h_chain : D ((√·) ∘ f) x₀ =? D (√·) (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sqrt h_f_pos] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSqrt' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ √(f x)) x₀
    (1 / (2 * √(f x₀)) * D₁) (c₁ ∧ f x₀ > 0) where
  eq := deriv_compSqrt.eq

private instance deriv_compExp {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (exp ∘ f) x₀
    (exp (f x₀) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (exp ∘ f) x₀ =? D exp (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Exp] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compExp' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ exp (f x)) x₀
    (exp (f x₀) * D₁) c₁ where
  eq := deriv_compExp.eq

private instance deriv_compLn {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (ln ∘ f) x₀
    (1 / (f x₀) * D₁) (c₁ ∧ f x₀ > 0) where
  eq := by
    intro ⟨h_cond, h_f_pos⟩
    have h_chain : D (ln ∘ f) x₀ =? D ln (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Ln h_f_pos] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compLn' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ ln (f x)) x₀
    (1 / (f x₀) * D₁) (c₁ ∧ f x₀ > 0) where
  eq := deriv_compLn.eq

private instance deriv_compSin {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sin ∘ f) x₀
    (cos (f x₀) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (sin ∘ f) x₀ =? D sin (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sin] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSin' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sin (f x)) x₀
    (cos (f x₀) * D₁) c₁ where
  eq := deriv_compSin.eq

private instance deriv_compCos {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (cos ∘ f) x₀
    (- sin (f x₀) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (cos ∘ f) x₀ =? D cos (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Cos] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCos' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ cos (f x)) x₀
    (- sin (f x₀) * D₁) c₁ where
  eq := deriv_compCos.eq

private instance deriv_compTan {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (tan ∘ f) x₀
    (sec (f x₀) ^2 * D₁) (c₁ ∧ (cos (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_cos_neq_zero⟩
    have h_chain : D (tan ∘ f) x₀ =? D tan (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Tan h_cos_neq_zero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compTan' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ tan (f x)) x₀
    (sec (f x₀) ^2 * D₁) (c₁ ∧ (cos (f x₀) ≠ 0)) where
  eq := deriv_compTan.eq

private instance deriv_compCot {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (cot ∘ f) x₀
    (- csc (f x₀) ^2 * D₁) (c₁ ∧ (sin (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_sin_neq_zero⟩
    have h_chain : D (cot ∘ f) x₀ =? D cot (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Cot h_sin_neq_zero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCot' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ cot (f x)) x₀
    (- csc (f x₀) ^2 * D₁) (c₁ ∧ (sin (f x₀) ≠ 0)) where
  eq := deriv_compCot.eq

private instance deriv_compSec {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sec ∘ f) x₀
    (tan (f x₀) * sec (f x₀) * D₁) (c₁ ∧ (cos (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_cos_neq_zero⟩
    have h_chain : D (sec ∘ f) x₀ =? D sec (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sec h_cos_neq_zero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSec' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sec (f x)) x₀
    (tan (f x₀) * sec (f x₀) * D₁) (c₁ ∧ (cos (f x₀) ≠ 0)) where
  eq := deriv_compSec.eq

private instance deriv_compCsc {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (csc ∘ f) x₀
    (- cot (f x₀) * csc (f x₀) * D₁) (c₁ ∧ (sin (f x₀) ≠ 0)) where
  eq := by
    intro ⟨h_cond, h_sin_neq_zero⟩
    have h_chain : D (csc ∘ f) x₀ =? D csc (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Csc h_sin_neq_zero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCsc' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ csc (f x)) x₀
    (- cot (f x₀) * csc (f x₀) * D₁) (c₁ ∧ (sin (f x₀) ≠ 0)) where
  eq := deriv_compCsc.eq

private instance deriv_compSinh {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sinh ∘ f) x₀
    (cosh (f x₀) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (sinh ∘ f) x₀ =? D sinh (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sinh] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSinh' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sinh (f x)) x₀
    (cosh (f x₀) * D₁) c₁ where
  eq := deriv_compSinh.eq

private instance deriv_compCosh {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (cosh ∘ f) x₀
    (sinh (f x₀) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (cosh ∘ f) x₀ =? D cosh (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Cosh] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCosh' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ cosh (f x)) x₀
    (sinh (f x₀) * D₁) c₁ where
  eq := deriv_compCosh.eq

private instance deriv_compTanh {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (tanh ∘ f) x₀
    (sech (f x₀) ^ 2 * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (tanh ∘ f) x₀ =? D tanh (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Tanh] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compTanh' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ tanh (f x)) x₀
    (sech (f x₀) ^ 2 * D₁) c₁ where
  eq := deriv_compTanh.eq

private instance deriv_compCoth {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (coth ∘ f) x₀
    (- csch (f x₀) ^ 2 * D₁) (c₁ ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_f_neq_zero⟩
    have h_chain : D (coth ∘ f) x₀ =? D coth (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Coth h_f_neq_zero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCoth' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ coth (f x)) x₀
    (- csch (f x₀) ^ 2 * D₁) (c₁ ∧ f x₀ ≠ 0) where
  eq := deriv_compCoth.eq

private instance deriv_compSech {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (sech ∘ f) x₀
    (- tanh (f x₀) * sech (f x₀) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (sech ∘ f) x₀ =? D sech (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Sech] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compSech' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ sech (f x)) x₀
    (- tanh (f x₀) * sech (f x₀) * D₁) c₁ where
  eq := deriv_compSech.eq

private instance deriv_compCsch {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (csch ∘ f) x₀
    (- coth (f x₀) * csch (f x₀) * D₁) (c₁ ∧ f x₀ ≠ 0) where
  eq := by
    intro ⟨h_cond, h_f_neq_zero⟩
    have h_chain : D (csch ∘ f) x₀ =? D csch (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Csch h_f_neq_zero] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compCsch' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ csch (f x)) x₀
    (- coth (f x₀) * csch (f x₀) * D₁) (c₁ ∧ f x₀ ≠ 0) where
  eq := deriv_compCsch.eq

private instance deriv_compArcsin {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arcsin ∘ f) x₀
    (1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := by
    intro ⟨h_cond, h_domain⟩
    have h_chain : D (arcsin ∘ f) x₀ =? D arcsin (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arcsin h_domain] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArcsin' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arcsin (f x)) x₀
    (1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := deriv_compArcsin.eq

private instance deriv_compArccos {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arccos ∘ f) x₀
    (-1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := by
    intro ⟨h_cond, h_domain⟩
    have h_chain : D (arccos ∘ f) x₀ =? D arccos (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arccos h_domain] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArccos' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arccos (f x)) x₀
    (-1 / √(1 - f x₀ ^ 2) * D₁) (c₁ ∧ (f x₀ > -1 ∧ f x₀ < 1)) where
  eq := deriv_compArccos.eq

private instance deriv_compArctan {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arctan ∘ f) x₀
    (1 / (1 + f x₀ ^ 2) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (arctan ∘ f) x₀ =? D arctan (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arctan] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArctan' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arctan (f x)) x₀
    (1 / (1 + f x₀ ^ 2) * D₁) c₁ where
  eq := deriv_compArctan.eq

private instance deriv_compArccot {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arccot ∘ f) x₀
    (-1 / (1 + f x₀ ^ 2) * D₁) c₁ where
  eq := by
    intro h_cond
    have h_chain : D (arccot ∘ f) x₀ =? D arccot (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arccot] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArccot' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arccot (f x)) x₀
    (-1 / (1 + f x₀ ^ 2) * D₁) c₁ where
  eq := deriv_compArccot.eq

private instance deriv_compArcsec {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arcsec ∘ f) x₀
    (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := by
    intro ⟨h_cond, h_domain⟩
    have h_chain : D (arcsec ∘ f) x₀ =? D arcsec (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arcsec h_domain] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArcsec' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arcsec (f x)) x₀
    (1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := deriv_compArcsec.eq

private instance deriv_compArccsc {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (arccsc ∘ f) x₀
    (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := by
    intro ⟨h_cond, h_domain⟩
    have h_chain : D (arccsc ∘ f) x₀ =? D arccsc (f x₀) * D f x₀ :=
      DerivExpr.Chain
    rw [DerivExpr.Arccsc h_domain] at h_chain
    rw [h_f.eq h_cond] at h_chain
    exact h_chain

private instance deriv_compArccsc' {f : ℝ → ℝ} {x₀ D₁ : ℝ} {c₁ : Prop}
    [h_f : AutoDeriv f x₀ D₁ c₁]
  : AutoDeriv (fun x ↦ arccsc (f x)) x₀
    (-1 / (|f x₀| * √(f x₀ ^ 2 - 1)) * D₁) (c₁ ∧ (f x₀ < -1 ∨ f x₀ > 1)) where
  eq := deriv_compArccsc.eq

@[aesop norm simp (rule_sets := [Derivative])]
private lemma auto_deriv {f : ℝ → ℝ} {x₀ : ℝ} {D₁ : ℝ} {cond : Prop}
    [AutoDeriv f x₀ D₁ cond] (h_cond : cond)
  : DerivExpr f x₀ = the D₁ := AutoDeriv.eq h_cond


/- ## Tactics -/

/-- ### Derivative Calculation
    __Usage__ `deriv`
    - `deriv` calculates derivative expressions as much as possible in standard
    forms, and then uses tactic `field` to solve the remaining goal.
    - Only used for derivative expression, such as `DerivExpr`
-/
macro "deriv" : tactic => `(tactic| {
  aesop (rule_sets := [ExprSimplify, Derivative])
})
