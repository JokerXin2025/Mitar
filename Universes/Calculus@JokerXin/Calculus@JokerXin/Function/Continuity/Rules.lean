import «Calculus@JokerXin».Function.Continuity.Defs
import «Calculus@JokerXin».Limit.Rules


/- ## 函数连续性的性质 Properties of Function's Continuity -/

/-- ### 函数极限复合（特别版本）
    ### Function Limit Composition (Special Version)
    - This version requires outer function `F` to be continuous at `u₀` -/
theorem FuncLimit.CompSV {x₀ u₀ L : ℝ} {F G : Function}
    (h_Nbhd : ∃ δ > 0, Nbhd x₀ δ ⊆ (F ⊙ G).domain)
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_F_cont : isContinuousAt F u₀)
  : FuncLimit (F ⊙ G) x₀ (F.map u₀)
:= sorry

/-- ### 函数极限复合（表达式特别版本）
    ### Function Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be continuous at `u₀` -/
theorem FuncLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim g x₀ = the u₀)
    (h_f_cont : lim f u₀ = the (f u₀))
  : lim (f ∘ g) x₀ = the (f u₀)
:= sorry

/-- ### 左极限复合（表达式特别版本）
    ### Left Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be left continuous at `u₀` -/
theorem LeftLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₋ g x₀ = the u₀)
    (h_f_cont : lim₋ f u₀ = the (f u₀))
  : lim₋ (f ∘ g) x₀ = the (f u₀)
:= sorry

/-- ### 右极限复合（表达式特别版本）
    ### Right Limit Composition (Expression's Special Version)
    - This version requires outer function `f` to be right continuous at `u₀` -/
theorem RightLimitExpr.CompSV {x₀ u₀ : ℝ} {f g : ℝ → ℝ}
    (h_u₀ : lim₊ g x₀ = the u₀)
    (h_f_cont : lim₊ f u₀ = the (f u₀))
  : lim₊ (f ∘ g) x₀ = the (f u₀)
:= sorry

/-- ### 函数加法的连续性
    ### Continuity of Function Addition -/
theorem Continuity.Add {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F + G) x₀
:= FuncLimit.Add h_f h_g

/-- ### 函数减法的连续性
    ### Continuity of Function Subtraction -/
theorem Continuity.Sub {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F - G) x₀
:= FuncLimit.Sub h_f h_g

/-- ### 函数乘法的连续性
    ### Continuity of Function Multiplication -/
theorem Continuity.Mul {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F * G) x₀
:= FuncLimit.Mul h_f h_g

/-- ### 函数除法的连续性
    ### Continuity of Function Division -/
theorem Continuity.Div {F G : Function} {x₀ : ℝ}
    (h_f : isContinuousAt F x₀) (h_g : isContinuousAt G x₀)
    (h_Gx₀_ne_0 : G.map x₀ ≠ 0)
  : isContinuousAt (F / G) x₀
:= FuncLimit.Div h_f h_g h_Gx₀_ne_0

/-- ### 函数复合的连续性
    ### Continuity of Function Composition -/
theorem Continuity.Comp {F G : Function} {x₀ u₀ : ℝ}
    (h_u₀ : FuncLimit G x₀ u₀)
    (h_f : isContinuousAt F u₀) (h_g : isContinuousAt G x₀)
  : isContinuousAt (F ⊙ G) x₀
:= sorry
