import Lean2TeX

set_option linter.defProp false

/- ============================================================
   Demo: cases/induction branch instrumentation test
   
   Tests how nested branch bodies are handled.
   Run: cd Lean2TeX && lake env lean Demo/Cases.lean
   ============================================================ -/

/- Bullet syntax: `·` is parsed as a standalone tactic node,
   so it appears in the output alongside `cases`. -/
#Lean2TeX theorem cases_bullet (b : Bool) : True := by
  cases b
  · trivial
  · trivial

/- Named `| ... =>` syntax: alternatives are inside the `cases`
   node and NOT extracted as separate tactics. Only `cases`
   appears at the top level. -/
#Lean2TeX theorem cases_named (b : Bool) : b = true ∨ b = false := by
  cases b with
  | false => right; rfl
  | true => left; rfl

/- Induction: same as `cases` — alternatives stay inside the node. -/
#Lean2TeX theorem induct_nat (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp
