import «Calculus@JokerXin».Prelude
import Mathlib.Tactic.GCongr.Core

variable {α : Type}

/-
  It's assumed that expression's type has instances of the following classes:
  - `Zero`
  - `Add`
  - `Sub`
  - `Mul`
  - `Div`
  - `DecidableEq`
-/

@[Lean2TeX "@2\\textcolor{lightgrey}{=}@3" Rel]
def UndeterminedEqual (A B : Option α) : Prop :=
  match B with
  | none => True
  | some B! =>
    A = the B!

infix:50 " =? " => UndeterminedEqual

@[refl]
theorem UndeterminedEqual_refl (A : Option α) : A =? A := by
  unfold UndeterminedEqual
  cases A with
  | none => trivial
  | some a => rfl

@[trans]
theorem UndeterminedEqual_trans {A B C : Option α}
    (h1 : A =? B) (h2 : B =? C) : A =? C := by
  unfold UndeterminedEqual at *
  cases C with
  | none => trivial
  | some c =>
    rw [h2] at h1
    exact h1

instance : Trans (@UndeterminedEqual α) (@UndeterminedEqual α) (@UndeterminedEqual α) where
  trans := UndeterminedEqual_trans

instance : Trans (@UndeterminedEqual α) (@Eq (Option α)) (@UndeterminedEqual α) where
  trans {A B C} h1 h2 := by
    rw [← h2]
    exact h1

instance : Trans (@Eq (Option α)) (@UndeterminedEqual α) (@UndeterminedEqual α) where
  trans {A B C} h1 h2 := by
    rw [h1]
    exact h2

private def free₂ (f : α → α → α) (a b : Option α) : Option α :=
  a.bind fun a => b.map <| f a

open Classical in
private noncomputable def div [Zero α] [Div α] (A B : Option α) : Option α :=
  if B = the 0 then none
  else free₂ (· / ·) A B

open Classical in
private noncomputable def pow [Pow α α] [Pow α ℤ] [Zero α] [One α] [LT α]
    [IntCast α] (A B : Option α) : Option α :=
  match A, B with
  | some x, some y =>
    if x = 0 ∧ y > 0 then the 0
    else if x > 0 then the (x ^ y)
    else if h : x < 0 ∧ (∃ n : ℤ, y = ↑n) then
      the (x ^ (choose h.2))
    else none
  | _, _ => none

instance [Add α]
  : Add (Option α) where add := free₂ (· + ·)
instance [Sub α]
  : Sub (Option α) where sub := free₂ (· - ·)
instance [Mul α]
  : Mul (Option α) where mul := free₂ (· * ·)
noncomputable instance [Zero α] [Div α]
  : Div (Option α) where div := div
noncomputable instance [Pow α α] [Pow α ℤ] [Zero α] [One α] [LT α] [IntCast α]
  : Pow (Option α) (Option α) where pow := pow
instance [Neg α]
  : Neg (Option α) where neg
    | the x => the (-x)
    | none  => none

@[gcongr]
theorem UndeterminedEqual_GcongrAdd {A B C : Option α}
    [Add α] (h : A =? B)
  : A + C =? B + C
:= by
  unfold UndeterminedEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UndeterminedEqual_GcongrAdd' {A B C : Option α}
    [Add α] (h : B =? C)
  : A + B =? A + C
:= by
  unfold UndeterminedEqual
  cases A with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UndeterminedEqual_GcongrSub {A B C : Option α}
    [Sub α] (h : A =? B)
  : A - C =? B - C
:= by
  unfold UndeterminedEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UndeterminedEqual_GcongrSub' {A B C : Option α}
    [Sub α] (h : B =? C)
  : A - B =? A - C
:= by
  unfold UndeterminedEqual
  cases A with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UndeterminedEqual_GcongrMul {A B C : Option α}
    [Mul α] (h : A =? B)
  : A * C =? B * C
:= by
  unfold UndeterminedEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UndeterminedEqual_GcongrMul' {A B C : Option α}
    [Mul α] (h : B =? C)
  : A * B =? A * C
:= by
  unfold UndeterminedEqual
  cases A with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

@[gcongr]
theorem UndeterminedEqual_GcongrDiv {A B C : Option α}
    [Zero α] [Div α] [DecidableEq α] (h : A =? B)
  : A / C =? B / C
:= sorry /-by
  cases B with
  | none =>
    have eq_none : none / C = none := by
      simp only [HDiv.hDiv, Div.div]
      split <;> rfl
    rw [eq_none]
    trivial
  | some b => rw [h]-/

@[gcongr]
theorem UndeterminedEqual_GcongrDiv' {A B C : Option α}
    [Zero α] [Div α] [DecidableEq α] (h : B =? C)
  : A / B =? A / C
:= by
  cases C with
  | none =>
    have eq_none : A / none = none := by
      cases A <;> rfl
    rw [eq_none]
    trivial
  | some c => rw [h]

lemma UdEqual.determine {A B : Option α} {B! : α}
    (h_udeq : A =? B) (h_B : B = the B!)
  : A = the B!
:= by
  rw [h_B] at h_udeq
  exact h_udeq

instance : Coe (ℝ → ℝ) (ℝ → Option ℝ) where
  coe := fun f x ↦ some (f x)
instance : Coe (ℕ → ℝ) (ℕ → Option ℝ) where
  coe := fun f n ↦ some (f n)

instance {n : Nat} [OfNat α n] : OfNat (Option α) n where
  ofNat := the (OfNat.ofNat n)
instance [OfScientific α] : OfScientific (Option α) where
  ofScientific := fun m s e ↦ the (OfScientific.ofScientific m s e)

@[simp]
lemma rewriteExpr_coe {a : α}
  : (a : Option α) = the a
:= rfl

@[simp]
lemma rewriteExpr_ofNat {n : ℕ} [OfNat α n]
  : (OfNat.ofNat n : Option α) = the (OfNat.ofNat n)
:= rfl
