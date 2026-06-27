import «Calculus@Mitar».Limit.Infinitesimal.Equivalent
import «Calculus@Mitar».Limit.Tactics.Simp

open Lean Elab Tactic


/-- Try to apply the rules of equivalence substitution -/
@[aesop unsafe 95% tactic (rule_sets := [LimitEquivalent])]
private def exe_EquivSubst : TacticM Unit := do
  evalTactic (← `(tactic|
    first
    | refine EquivSubst (SinEquiv ?_)
    | refine EquivSubst (TanEquiv ?_)
    | refine EquivSubst (ExpEquiv ?_)
    | refine EquivSubst (PowEquiv ?_)
    | refine EquivSubst' (SinEquiv ?_)
    | refine EquivSubst' (TanEquiv ?_)
    | refine EquivSubst' (ExpEquiv ?_)
    | refine EquivSubst' (PowEquiv ?_)
    | refine EquivSubst_Left (SinEquiv_Left ?_)
    | refine EquivSubst_Left (TanEquiv_Left ?_)
    | refine EquivSubst_Left (ExpEquiv_Left ?_)
    | refine EquivSubst_Left (PowEquiv_Left ?_)
    | refine EquivSubst_Left' (SinEquiv_Left ?_)
    | refine EquivSubst_Left' (TanEquiv_Left ?_)
    | refine EquivSubst_Left' (ExpEquiv_Left ?_)
    | refine EquivSubst_Left' (PowEquiv_Left ?_)
    | refine EquivSubst_Right (SinEquiv_Right ?_)
    | refine EquivSubst_Right (TanEquiv_Right ?_)
    | refine EquivSubst_Right (ExpEquiv_Right ?_)
    | refine EquivSubst_Right (PowEquiv_Right ?_)
    | refine EquivSubst_Right' (SinEquiv_Right ?_)
    | refine EquivSubst_Right' (TanEquiv_Right ?_)
    | refine EquivSubst_Right' (ExpEquiv_Right ?_)
    | refine EquivSubst_Right' (PowEquiv_Right ?_)
  ))


/-- ### Limit Expression Equivalence Substitution3
    __Usage__ `lim_equiv`
    - `lim_equiv` uses the rule of equivalent infinitesimal substitution to
      simplify the limit expression:
-/
macro "lim_equiv" : tactic => `(tactic| {
  -- Apply `=?`'s generalized congruence first --
  try gcongr
  -- Use tactic `lim_simp` to prove the equivalence --
  aesop (rule_sets := [LimitSimplify, LimitEquivalent])
})
