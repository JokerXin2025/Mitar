import «Calculus@JokerXin».Function.Continuity.Elementary
import «Calculus@JokerXin».Function.Differential.Tactic


/- ## Preparations -/

private theorem L'Hospital_x₀_zero {f g : ℝ → ℝ} {x₀ L : ℝ}
    (h_f : lim f x₀ = the 0) (h_g : lim g x₀ = the 0)
    (h_deriv : lim (fun x ↦ D f x / D g x) x₀ = L)
  : lim (f / g) x₀ = the L
:= sorry

private theorem L'Hospital_x₀_zero' {f g : ℝ → ℝ} {x₀ L : ℝ}
    (h_f : lim f x₀ = the 0) (h_g : lim g x₀ = the 0)
    (h_deriv : lim (fun x ↦ D f x / D g x) x₀ = L)
  : lim (fun x ↦ f x / g x) x₀ = the L
:= sorry


/- ## Tactics -/

/-- ### Application of L'Hôpital's Rules
    __Usage__ `lim_luo`
-/
macro "lim_luo" : tactic => `(tactic| {
  first
  | apply L'Hospital_x₀_zero
  | apply L'Hospital_x₀_zero'
  all_goals try aesop (rule_sets := [ExprSimplify, LimitBasic, Derivative])
})
