import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Limit.Rules
import «Calculus@JokerXin».Function.Continuity.Elementary

open Lean Elab Tactic


/- ## Preparations -/

@[aesop unsafe 10% tactic (rule_sets := [LimitBasic])]
private def exe_norm_num : TacticM Unit := do
  evalTactic (← `(tactic| norm_num))

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private lemma Comp_id {f : ℝ → ℝ} {x₀ : ℝ}
    (h_comp : lim (f ∘ (·)) x₀ = the (f x₀))
  : lim f x₀ = the (f x₀)
:= h_comp

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem FuncLimit_Add {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim f x₀ = the L1) (h_G : lim g x₀ = the L2)
  : lim (f + g) x₀ = the (L1 + L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem LeftLimit_Add {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim₋ f x₀ = the L1) (h_G : lim₋ g x₀ = the L2)
  : lim₋ (f + g) x₀ = the (L1 + L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem RightLimit_Add {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim₊ f x₀ = the L1) (h_G : lim₊ g x₀ = the L2)
  : lim₊ (f + g) x₀ = the (L1 + L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem FuncLimit_Sub {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim f x₀ = the L1) (h_G : lim g x₀ = the L2)
  : lim (f - g) x₀ = the (L1 - L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem LeftLimit_Sub {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim₋ f x₀ = the L1) (h_G : lim₋ g x₀ = the L2)
  : lim₋ (f - g) x₀ = the (L1 - L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem RightLimit_Sub {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim₊ f x₀ = the L1) (h_G : lim₊ g x₀ = the L2)
  : lim₊ (f - g) x₀ = the (L1 - L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem FuncLimit_Mul {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim f x₀ = the L1) (h_G : lim g x₀ = the L2)
  : lim (f * g) x₀ = the (L1 * L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem LeftLimit_Mul {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim₋ f x₀ = the L1) (h_G : lim₋ g x₀ = the L2)
  : lim₋ (f * g) x₀ = the (L1 * L2)
:= sorry

@[aesop unsafe 50% apply (rule_sets := [LimitBasic])]
private theorem RightLimit_Mul {f g : ℝ → ℝ} {x₀ L1 L2 : ℝ}
    (h_F : lim₊ f x₀ = the L1) (h_G : lim₊ g x₀ = the L2)
  : lim₊ (f * g) x₀ = the (L1 * L2)
:= sorry


/- ## Tactics -/

/-- ### Limit Expression Simplification
    __Usage__ `lim_simp`
    - `lim_simp` uses the following methods to simplify the limit expression
      (at most to a constant):
      - __Continuity__: Limit of a continuous function is the function value.
      - __Variable Substitution__: Rewrite the expression and `x₀` with
        the outer function and limit of the inner function
    - Only used for limit expression, such as `FuncLimitExpr`
-/
macro "lim_simp" : tactic => `(tactic|
  aesop (rule_sets := [ExprSimplify, LimitBasic])
)
