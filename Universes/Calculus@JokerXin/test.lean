import «Calculus@JokerXin»
import Mathlib

variable {C x : ℝ}

example (_ : x > 0)
  : lim (ln ∘ sin) x = the (ln (sin x))
:= by lim_simp

example
  : D (exp + sin) x = the (exp x + cos x + 0 * x)
:= by deriv

example (_ : sin x > 0) (_ : sin x ≠ 0)
  : D (ln ∘ sin) x = the (cos x / sin x)
:= by deriv

example (_ : x > 0) (_ : x ≠ 0)
  : D (fun x ↦ ln x + x) x = the (1 / x + 1)
:= by deriv

example (_ : x > 0) (_ : x ≠ 0)
  : D (ln + (·)) x = the (1 / x + 1)
:= by deriv

example
  : 1 + D (fun x => x * x + sin x) x = the (1 + 2 * x + cos x)
:= by deriv

example
  : D (ln ∘ ((·) + (·))) 1 = the 1
:= by deriv

example
  : lim (fun x ↦ x / x) 0 = the 1
:= by lim_luo

example
  : D (fun x ↦ (x + 3)) x = the 1
:= by deriv



-- ### 基础函数测试

example
  : D (fun _ ↦ C) x = the 0
:= by deriv

example
  : D (fun _ ↦ exp 1) x = the 0
:= by deriv

example
  : D (fun x ↦ x) x = the 1
:= by deriv

example (_ : x ≠ 0)
  : D (fun x ↦ |x|) x = the (x / |x|)
:= by deriv


example (_ : x > 0)
  : D (fun x ↦ √x) x = the (1 / (2 * √x))
:= by deriv

example
  : D (fun x ↦ exp x) x = the (exp x)
:= by deriv

example (_ : x > 0) (_ : x ≠ 0)
  : D (fun x ↦ ln x) x = the (1 / x)
:= by deriv


-- ### 三角函数测试

example
  : D (fun x ↦ sin x) x = the (cos x)
:= by deriv

example
  : D (fun x ↦ cos x) x = the (- sin x)
:= by deriv

example (_ : cos x ≠ 0)
  : D (fun x ↦ tan x) x = the (sec x ^2)
:= by deriv

example (_ : sin x ≠ 0)
  : D (fun x ↦ cot x) x = the (- csc x ^2)
:= by deriv

example : 2 ^ 2 = 4 := by norm_nnum

example (_ : cos x ≠ 0)
  : D (fun x ↦ sec x) x = the (sec x * tan x)
:= by deriv

example (_ : sin x ≠ 0)
  : D (fun x ↦ csc x) x = the (- csc x * cot x)
:= by deriv


-- ### 双曲函数测试

example
  : D (fun x ↦ sinh x) x = the (cosh x)
:= by deriv

example
  : D (fun x ↦ cosh x) x = the (sinh x)
:= by deriv

example
  : D (fun x ↦ tanh x) x = the (sech x ^2)
:= by deriv

example (_ : x ≠ 0)
  : D (fun x ↦ coth x) x = the (- csch x ^2)
:= by deriv

example
  : D (fun x ↦ sech x) x = the (- sech x * tanh x)
:= by deriv

example (_ : x ≠ 0)
  : D (fun x ↦ csch x) x = the (- csch x * coth x)
:= by deriv


-- ### 反三角函数测试

example (_ : x > -1 ∧ x < 1)
  : D (fun x ↦ arcsin x) x = the (1 / √(1 - x^2))
:= by deriv

example (_ : x > -1 ∧ x < 1)
  : D (fun x ↦ arccos x) x = the (-1 / √(1 - x^2))
:= by deriv

example
  : D (fun x ↦ arctan x) x = the (1 / (1 + x^2))
:= by deriv

example
  : D (fun x ↦ arccot x) x = the (-1 / (1 + x^2))
:= by deriv

example (_ : x < -1 ∨ x > 1)
  : D (fun x ↦ arcsec x) x = the (1 / (|x| * √(x^2 - 1)))
:= by deriv

example (_ : x < -1 ∨ x > 1)
  : D (fun x ↦ arccsc x) x = the (-1 / (|x| * √(x^2 - 1)))
:= by deriv

-- ### 四则运算与多项式测试

example
  : D (fun x ↦ 3 + cos x) x = the (cos x - x * sin x)
:= by deriv


example (_ : x > 0) : D (fun x ↦ x * ln x) x = the (1 + 1 / x)
:= by deriv

example
  : D (fun x ↦ sin x - exp x) x = the (cos x - exp x)
:= by deriv

example
  : D (fun x ↦ x * cos x) x = the (cos x - x * sin x)
:= by deriv

example
  : D (fun x ↦ exp x / x) x = the (x * exp x - exp x / x^2)
:= by deriv

example
  : D (fun x ↦ 3 * x^2 + 2 * x + 1) x = the (6 * x + 2)
:= by deriv

example
  : D (fun x ↦ (x + 1) * (x - 1)) x = the (2 * x)
:= by deriv

example
  : D (fun x ↦ (x^3 - 1) / (x - 1)) x = the (2 * x + 1)
:= by deriv

example
  : D (fun x ↦ x / (x + 1) + 1 / (x + 1)) x = the 0
:= by deriv


-- ### 复合函数与链式法则测试

example
  : D (fun x ↦ sin (cos x)) x = the (- sin x * cos (cos x))
:= by deriv

example
  : D (fun x ↦ exp (2 * x)) x = the (2 * exp (2 * x))
:= by deriv

example
  : D (fun x ↦ √(x^2 + 1)) x = the ((2 * x) / (2 * √(x^2 + 1)))
:= by deriv

example (_ : sin x > 0) (_ : sin x ≠ 0)
  : D (fun x ↦ ln (sin x)) x = the (cos x / sin x)
:= by deriv

example
  : D (fun x ↦ (x + 1)^3) x = the (3 * (x + 1)^2)
:= by deriv

example (_ : cos (exp x) ≠ 0)
  : D (fun x ↦ tan (exp x)) x = the (exp x * (sec (exp x))^2)
:= by deriv
example
  : D (fun x ↦ arcsin (ln x)) x = the ((1 / x) / √(1 - (ln x)^2))
:= by deriv

example
  : D (fun x ↦ cosh (√x)) x = the (sinh (√x) / (2 * √x))
:= by deriv

example
  : D (fun x ↦ x^2 * ln x) x = the (2 * x * ln x + x)
:= by deriv

example
  : D (fun x ↦ (sin x)^2) x = the (2 * sin x * cos x)
:= by deriv

example
  : D (fun x ↦ 1 / (1 + x^2)) x = the (-2 * x / (1 + x^2)^2)
:= by deriv

example
  : D (fun x ↦ exp (-x^2)) x = the (-2 * x * exp (-x^2))
:= by deriv

example
  : D (fun x ↦ |x^2 - 1|) x = the (((x^2 - 1) / |x^2 - 1|) * (2 * x))
:= by deriv

example
  : D (fun x ↦ arctan (sinh x)) x = the (cosh x / (1 + (sinh x)^2))
:= by deriv


-- ### 复杂表达式等价性压力测试

example
  : D (fun x ↦ (exp x)^2 - exp (2 * x)) x = the 0
:= by deriv

example (_ : cos x ≠ 0)
  : D (fun x ↦ sec x + tan x) x = the (sec x * tan x + sec x ^2)
:= by deriv
example
  : D (fun x ↦ ln (x + √(x^2 + 1))) x = the ((1 + (2 * x) / (2 * √(x^2 + 1))) / (x + √(x^2 + 1)))
:= by deriv



axiom SomeFunc : (ℝ → ℝ) → ℝ

class AutoClass (f : ℝ → ℝ) (val : outParam ℝ) where
  eq : SomeFunc f = val

instance auto_const {C : ℝ} : AutoClass (fun _ ↦ C) 0 := sorry
instance auto_id : AutoClass (·) 0 := sorry
instance auto_add {f g : ℝ → ℝ} {val₁ val₂ : ℝ}
    [AutoClass f val₁] [AutoClass g val₂]
  : AutoClass (fun x ↦ f x + g x) (val₁ + val₂)
:= sorry

@[simp]
lemma auto_simp {f : ℝ → ℝ} {val : ℝ} [AutoClass f val]
  : SomeFunc f = val := AutoClass.eq

example
  : SomeFunc (·) = 0 := by simp only [auto_simp]
example
  : SomeFunc (fun _ ↦ 1) = 0 := by simp only [auto_simp]
example
  : SomeFunc (fun x ↦ x + x) = 0 := by simp only [auto_simp, add_zero]
lemma h
  : SomeFunc (fun x ↦ x + 3) = 0 := of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.trans auto_simp (add_zero 0))) 0) (eq_self 0))
set_option trace.Meta.synthInstance true
example
  : SomeFunc (fun x ↦ 3 + x) = 0 := of_eq_true (Eq.trans (congrFun' (congrArg Eq (Eq.trans auto_simp (add_zero 0))) 0) (eq_self 0))
