import «Calculus@Mitar».Expr.Prelude
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

private def map₂ (f : α → α → α) (a b : Option α) : Option α :=
  a.bind fun a => b.map <| f a

instance [Add α] : Add (Option α) where
  add := map₂ (· + ·)
instance [Sub α] : Sub (Option α) where
  sub := map₂ (· - ·)
instance [Mul α] : Mul (Option α) where
  mul := map₂ (· * ·)
instance [Zero α] [Div α] [DecidableEq α] : Div (Option α) where
  div A B :=
    if B = the 0 then none
    else
      map₂ (· / ·) A B

private theorem UndeterminedEqual_map₂ {A B C : Option α} (op : α → α → α) (h : A =? B)
    : map₂ op A C =? map₂ op B C := by
  unfold UndeterminedEqual
  cases B with
  | none => trivial
  | some b =>
    cases C with
    | none => trivial
    | some c =>
      rw [h]
      rfl

private theorem UndeterminedEqual_map₂' {A B C : Option α} (op : α → α → α) (h : B =? C)
    : map₂ op A B =? map₂ op A C := by
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
theorem UndeterminedEqual_GcongrAdd {A B C : Option α}
    [Add α] (h : A =? B)
    : A + C =? B + C
:= UndeterminedEqual_map₂ (· + ·) h

@[gcongr]
theorem UndeterminedEqual_GcongrAdd' {A B C : Option α}
    [Add α] (h : B =? C)
    : A + B =? A + C
:= UndeterminedEqual_map₂' (· + ·) h

@[gcongr]
theorem UndeterminedEqual_GcongrSub {A B C : Option α}
    [Sub α] (h : A =? B)
    : A - C =? B - C
:= UndeterminedEqual_map₂ (· - ·) h

@[gcongr]
theorem UndeterminedEqual_GcongrSub' {A B C : Option α}
    [Sub α] (h : B =? C)
    : A - B =? A - C
:= UndeterminedEqual_map₂' (· - ·) h

@[gcongr]
theorem UndeterminedEqual_GcongrMul {A B C : Option α}
    [Mul α] (h : A =? B)
    : A * C =? B * C
:= UndeterminedEqual_map₂ (· * ·) h

@[gcongr]
theorem UndeterminedEqual_GcongrMul' {A B C : Option α}
    [Mul α] (h : B =? C)
    : A * B =? A * C
:= UndeterminedEqual_map₂' (· * ·) h

@[gcongr]
theorem UndeterminedEqual_GcongrDiv {A B C : Option α}
    [Zero α] [Div α] [DecidableEq α] (h : A =? B)
    : A / C =? B / C
:= by
  cases B with
  | none =>
    have eq_none : none / C = none := by
      change (if C = the 0 then none else map₂ (· / ·) none C) = none
      split <;> rfl
    rw [eq_none]
    trivial
  | some b => rw [h]

@[gcongr]
lemma UndeterminedEqual_GcongrDiv' {A B C : Option α}
    [Zero α] [Div α] [DecidableEq α] (h : B =? C)
    : A / B =? A / C
:= by
  cases C with
  | none =>
    have eq_none : A / none = none := by
      change (if none = the 0 then none else map₂ (· / ·) A none) = none
      cases A <;> rfl
    rw [eq_none]
    trivial
  | some c => rw [h]

theorem UndeterminedEqual_Determine {A B : Option α} {B! : α}
    (h_udeq : A =? B) (h_B : B = the B!)
    : A = the B!
:= by
  rw [h_B] at h_udeq
  exact h_udeq
