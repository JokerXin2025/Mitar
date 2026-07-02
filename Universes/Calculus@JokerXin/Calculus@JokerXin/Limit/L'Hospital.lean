import «Calculus@JokerXin».Limit.Expr
import «Calculus@JokerXin».Function.Differential.Defs


/- 不提供表达式版本，因为求导的结果可能存在多样性，在表达式计算中请使用tactic版本 -/

/-- ### 洛必达法则（`x → x₀`、0/0型）
    ### L'Hospital's Rule (`x → x₀`, 0/0 Type) -/
theorem FuncLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : FuncLimit F x₀ 0) (h_G : FuncLimit G x₀ 0)
    (h_deriv : FuncLimit ((Diff F) / (Diff G)) x₀ L)
  : FuncLimit (F / G) x₀ L
:= sorry

/-- ### 洛必达法则（`x → x₀`、0/0型、左极限）
    ### L'Hospital's Rule (`x → x₀`, 0/0 Type, Left Limit) -/
theorem LeftLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : LeftLimit F x₀ 0) (h_G : LeftLimit G x₀ 0)
    (h_deriv : LeftLimit ((Diff F) / (Diff G)) x₀ L)
  : LeftLimit (F / G) x₀ L
:= sorry

/-- ### 洛必达法则（`x → x₀`、0/0型、右极限）
    ### L'Hospital's Rule (`x → x₀`, 0/0 Type, Right Limit) -/
theorem RightLimit.L'Hospital_x₀_zero {F G : Function} {x₀ L : ℝ}
    (h_F : RightLimit F x₀ 0) (h_G : RightLimit G x₀ 0)
    (h_deriv : RightLimit ((Diff F) / (Diff G)) x₀ L)
  : RightLimit (F / G) x₀ L
:= sorry
