import «Calculus@JokerXin».Function.Continuity.Rules
import «Calculus@JokerXin».Function.Tactics.ToFunction
import «Calculus@JokerXin».Limit.Tactics.Simplify

open Lean Elab Tactic


/- ## Preparations -/

@[aesop safe apply (rule_sets := [FunctionContinuity])]
private lemma fold_isContinuousAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : FuncLimit F x₀ (F.map x₀)
:= by assumption

@[aesop safe tactic (rule_sets := [FunctionContinuity])]
private def exe_trivial : TacticM Unit := do
  evalTactic (← `(tactic| solve | trivial))

@[aesop safe tactic (rule_sets := [FunctionContinuity])]
private def exe_linarith : TacticM Unit := do
  evalTactic (← `(tactic| solve | linarith))


/- ## Tactics -/

/--
  ### Prover of Function Continuity
  __Usage__ `continuity_at x₀` where `x₀` is the
-/
macro "continuity_at" x₀:ident : tactic => `(tactic| {
  to_Function $x₀
  aesop (rule_sets := [FunctionContinuity])
})


/- ## Examples -/

example (x₀ : ℝ)
  : isContinuousAt (Sin + Cos) x₀
:= by continuity_at x₀

example (x₀ : ℝ)
  : isContinuousAt (Sin + Cos) x₀
:= by
  apply Continuity.Add
  · continuity_at x₀
  · continuity_at x₀

example (x₀ : ℝ)
  : FuncLimit (Sin + Cos) x₀ (sin x₀ + cos x₀)
:= by continuity_at x₀
