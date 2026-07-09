import «Calculus@JokerXin».Function.Concept
import «Calculus@JokerXin».Function.Continuity.Defs


/- ## 闭区间上的连续函数 Continuous Functions on Closed Interval -/

/-- ### 最小值定理
    ### The Minimum Values Theorem -/
theorem Min_Existence {F : Function} {l r : ℝ}
    (h_l_lt_r : l < r)
    (h_cont : isContinuousInIcc F l r)
  : ∃ m ∈ Icc l r, isMinimumPoint F m
:= sorry

/-- ### 最大值定理
    ### The Maximum Values Theorem -/
theorem Max_Existence {F : Function} {l r : ℝ}
    (h_l_lt_r : l < r)
    (h_cont : isContinuousInIcc F l r)
  : ∃ m ∈ Icc l r, isMaximumPoint F m
:= sorry

/-- ### 介值定理
    ### The Intermediate Value Theorem -/
theorem Interm_Existence {F : Function} {l r C : ℝ}
    (h_l_lt_r : l < r)
    (h_interm : F.map l < C ∧ C < F.map r
                ∨ F.map r < C ∧ C < F.map l)
    (h_cont : isContinuousInIcc F l r)
  : ∃ c ∈ Ioo l r, F.map c = C
:= sorry
