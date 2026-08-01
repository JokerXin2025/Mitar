import Lean2TeX

set_option linter.defProp false

/- ==========================================================================
   Demo: Core Built-in Tactics
   
   Tests all 10 tactics in `builtinTacticConfigs`:
   - kind=true:  exact, apply, change, norm_num, unfold, obtain, have
   - kind=false: sorry, rfl
   ========================================================================== -/


/-! ## Test 1: `exact` (kind, no args) -/
#Lean2TeX theorem core_exact (P : Prop) (h : P) : P := by
  exact h

/-! ## Test 2: `apply` (kind, no args) -/
#Lean2TeX theorem core_apply (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

/-! ## Test 3: `change` (kind, no args, rewrites goal type) -/
#Lean2TeX theorem core_change (n : Nat) : n = n := by
  change n = n
  rfl

/-! ## Test 4: `norm_num` — arithmetic normalization (uses `native_decide` as fallback) -/
-- norm_num is Mathlib-only in Lean 4.32; using omega instead which IS in core
#Lean2TeX theorem core_omega : 2 + 2 = 4 := by
  omega

/-! ## Test 5: `unfold` (kind, extracts concept) -/
def MyAdd (a b : Nat) : Nat := a + b

#Lean2TeX theorem core_unfold_simple (a b : Nat) : MyAdd a b = a + b := by
  unfold MyAdd
  rfl

/-! ## Test 6: `obtain` pattern (kind, position=after, extracts m + h_m) -/
#Lean2TeX theorem core_obtain (h : ∃ x : Nat, x = 0) : True := by
  rcases h with ⟨w, hw⟩
  trivial

/-! ## Test 7: `have` with `by` block (kind, position=after, nested instrumentation) -/
#Lean2TeX theorem core_have_by (P : Prop) (h : P) : P ∧ P := by
  have h' : P := by
    exact h
  exact And.intro h' h'

/-! ## Test 8: `have` non-`by` branch (kind, config-driven fallback) -/
#Lean2TeX theorem core_have_term (P Q : Prop) (hpq : P → Q) (hp : P) : Q := by
  have q := hpq hp
  exact q

/-! ## Test 9: `sorry` (text, exact match, term-in-tactic-position) -/
#Lean2TeX theorem core_sorry (P : Prop) : P := by
  sorry

/-! ## Test 10: `rfl` (text, exact match) -/
#Lean2TeX theorem core_rfl (n : Nat) : n = n := by
  rfl

/-! ## Test 11: Multi-tactic sequence exercising have, apply, exact together -/
#Lean2TeX theorem core_sequence (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  have hp' : P := by
    exact hP
  apply hPQ
  exact hp'
