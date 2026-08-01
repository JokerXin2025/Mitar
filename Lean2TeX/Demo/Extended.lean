import Lean2TeX

-- Load Mathlib extension tactic configs (53 entries)
-- Makes text-based matching available for intro, cases, constructor, rw, simp, ...
#load_tactics "Lean2TeX/tactics_mathlib.json"

set_option linter.defProp false

/- ==========================================================================
   Demo: Extended Tactics (via `tactics_mathlib.json`)
   
   All tactics below are in Lean core.  They are matched via
   `kind=false` text-based entries loaded by `#load_tactics`.
   
   Run:  cd Lean2TeX && lake env lean Demo/Extended.lean
   Output:  Demo/Extended/*_Lean2TeX.json
   ========================================================================== -/


/-! ## Test 1: `intro` (text prefix) -/
#Lean2TeX theorem ext_intro (P Q : Prop) : P → Q → P := by
  intro hP hQ
  exact hP

/-! ## Test 2: `intros` (text prefix, bundles multiple intro's) -/
#Lean2TeX theorem ext_intros (P Q R : Prop) : P → Q → R → P := by
  intros hP hQ hR
  exact hP

/-! ## Test 3: `refine` (text prefix, partial proof term) -/
#Lean2TeX theorem ext_refine (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  refine h ?_
  exact hp

/-! ## Test 4: `constructor` (text prefix, splits ∧) -/
#Lean2TeX theorem ext_constructor (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

/-! ## Test 5: `left` / `right` (text exact, ∨ selection) -/
#Lean2TeX theorem ext_left (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

#Lean2TeX theorem ext_right (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

/-! ## Test 6: `assumption` (text exact, closes from context) -/
#Lean2TeX theorem ext_assumption (P : Prop) (h : P) : P := by
  assumption

/-! ## Test 7: `trivial` (text exact) -/
#Lean2TeX theorem ext_trivial : True := by
  trivial

/-! ## Test 8: `contradiction` (text exact, False in context) -/
#Lean2TeX theorem ext_contradiction (P : Prop) (h : False) : P := by
  exact False.elim h

/-! ## Test 9: `exfalso` (text exact, replaces goal with False) -/
#Lean2TeX theorem ext_exfalso (P : Prop) (h : ¬ P) (hp : P) : False := by
  apply h
  exact hp

/-! ## Test 10: `cases` (text prefix, case analysis on Bool) -/
#Lean2TeX theorem ext_cases (b : Bool) : b = true ∨ b = false := by
  cases b
  · right; rfl
  · left; rfl

/-! ## Test 11: `rw` (text prefix, rewrite with hypothesis) -/
#Lean2TeX theorem ext_rw (a b : Nat) (h : a = b) : a = b := by
  rw [h]

/-! ## Test 12: `simp` (text prefix, simplification) -/
#Lean2TeX theorem ext_simp (n : Nat) : n + 0 = n := by
  simp

/-! ## Test 13: `dsimp` (text prefix, definitional simplification) -/
def MyId (x : Nat) : Nat := x

#Lean2TeX theorem ext_dsimp (n : Nat) : MyId n = n := by
  dsimp [MyId]

/-! ## Test 14: `by_cases` (text prefix, case split on proposition) -/
#Lean2TeX theorem ext_by_cases (P : Prop) [Decidable P] : True := by
  by_cases h : P
  · trivial
  · trivial

/-! ## Test 15: `by_contra` (text prefix, proof by contradiction) -/
#Lean2TeX theorem ext_by_contra (P : Prop) (h : ¬¬ P) : P := by
  apply Classical.byContradiction
  intro hnp
  exact h hnp

/-! ## Test 16: `specialize` (text prefix, instantiate hypothesis) -/
#Lean2TeX theorem ext_specialize (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  have hq := h hp
  exact hq

/-! ## Test 17: `induction` (text prefix, induction on Nat) -/
#Lean2TeX theorem ext_induction (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => 
    simp

/-! ## Test 18: Mixed text + core tactics in a single proof -/
#Lean2TeX theorem ext_mixed (P Q : Prop) (h : P ∧ Q) : Q := by
  cases h
  case intro hp hq =>
    assumption
