import «Calculus@JokerXin».Limit.Infinitesimal.Equivalent
import «Calculus@JokerXin».Limit.Tactics.Simplify

open Lean Elab Tactic


/- ## Preparations -/

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst_SinEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst (SinEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst_TanEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst (TanEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst_ExpEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst (ExpEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst_PowEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst (PowEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst'_SinEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst' (SinEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst'_TanEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst' (TanEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst'_ExpEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst' (ExpEquiv ?_)))

@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
def apply_EquivSubst'_PowEquiv : TacticM Unit := do
  evalTactic (← `(tactic| refine EquivSubst' (PowEquiv ?_)))


/- ## Tactics -/

/-- ### Limit Expression Equivalence Substitution3
    __Usage__ `lim_equiv`
    - `lim_equiv` uses the rule of equivalent infinitesimal substitution to
      simplify the limit expression:
-/
macro "lim_equiv" : tactic => `(tactic| {
  -- Apply `=?`'s generalized congruence first --
  try gcongr
  -- Use tactic `lim_simp` to prove the equivalence --
  aesop (rule_sets := [LimitBasic, LimitEquivalent])
})
