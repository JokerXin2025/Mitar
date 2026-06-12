import «Calculus@Mitar».Sequence.Basic
import «Calculus@Mitar».Sequence.Limit


/- # 数列极限计算法则 Calculation Rules of Sequence Limit -/

--  加法法则 | Addition Rule
theorem SeqLimitAdd {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B) :
    SeqLimit (fun n => a n + b n) (A + B) := by
  sorry

--  减法法则 | Subtraction Rule
theorem SeqLimitSub {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B) :
    SeqLimit (fun n => a n - b n) (A - B) := by
  sorry

--  乘法法则 | Multiplication Rule
theorem SeqLimitMul {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B) :
    SeqLimit (fun n => a n * b n) (A * B) := by
  sorry

--  除法法则 | Division Rule
theorem SeqLimitDiv {a b : Sequence} {A B : ℝ}
    (h_a : SeqLimit a A) (h_b : SeqLimit b B)
    (h_B_ne0 : B ≠ 0) (h_b_ne0 : ∀ n, b n ≠ 0) :
    SeqLimit (fun n => a n / b n) (A / B) := by
  sorry

--  夹逼定理 | Squeeze Theorem
theorem SeqLimitSqueeze {a b c : Sequence} {A : ℝ}
    (h_a : SeqLimit a A) (h_c : SeqLimit c A)
    (h_chain : ∀ n, a n ≤ b n ∧ b n ≤ c n) :
    SeqLimit b A := by
  sorry
