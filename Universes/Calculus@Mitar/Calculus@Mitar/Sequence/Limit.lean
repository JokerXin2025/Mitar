import «Calculus@Mitar».Sequence.Basic


/- # 数列极限 Sequence Limit -/

--  极限 | Limit
def SeqLimit (a : Sequence) (A : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |a n - A| < ε

--  收敛 | Converges
def SeqConverges (a : Sequence) : Prop :=
  ∃ A : ℝ, SeqLimit a A


/- # 数列极限的性质 Properties of Sequence Limit -/

--  唯一 | Unique
theorem SeqLimit_Unique {a : Sequence} {A B : ℝ}
    (hA : SeqLimit a A) (hB : SeqLimit a B) : A = B := by
  sorry

--  保号 | Sign-Preserving
theorem SeqLimit_pos {a : Sequence} {A : ℝ}
    (h_lim : SeqLimit a A) (h_A_pos : A > 0) :
    ∃ N : ℕ, ∀ n > N, a n > 0 := by
  sorry
theorem SeqLimit_neg {a : Sequence} {A : ℝ}
    (h_lim : SeqLimit a A) (h_A_neg : A < 0) :
    ∃ N : ℕ, ∀ n > N, a n < 0 := by
  sorry

--  收敛 => 有界 | Converges => Bounded
theorem SeqConverges_Bounded {a : Sequence}
    (h : SeqConverges a) : SeqBounded a := by
  sorry
