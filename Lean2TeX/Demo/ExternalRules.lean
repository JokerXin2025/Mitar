import Lean2TeX

set_option linter.defProp false

/-! ============================================================
   Demo: External pipeline rules
   
   Loads `Lean2TeX/pipeline_rules.json` via `#load_pipeline_rules`
   to configure structural tactics (cases/induction/rcases) and
   calc relation mappings from an external file.
   ============================================================ -/

#load_pipeline_rules "Lean2TeX/pipeline_rules.json"

/- `cases` with multi-line branches (from external config) -/
#Lean2TeX theorem ext_cases_multi (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero =>
    left
    rfl
  | succ k =>
    right
    apply Nat.succ_pos

/- `calc` block with external relation mappings -/
#Lean2TeX theorem ext_calc (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc
    a = b := h1
    _ = c := h2

/- `rcases` with bullet branch -/
#Lean2TeX theorem ext_rcases (p : Nat × Nat) : p.1 = p.1 := by
  rcases p with ⟨a, b⟩
  · rfl
