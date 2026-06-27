import «Calculus@Mitar».Prelude


/- # 数列 Sequence -/

--  数列 | Sequence
abbrev Sequence := ℕ → ℝ


/- # 数列有界性 Boundedness of Sequence -/

--  有界 | Bounded
def SeqBounded (a : Sequence) : Prop :=
  ∃ M > 0, ∀ n, |a n| < M

--  有上界 | Upper-Bounded
def SeqUpperBounded (a : Sequence) : Prop :=
  ∃ M > 0, ∀ n, a n < M

--  有下界 | Lower-Bounded
def SeqLowerBounded (a : Sequence) : Prop :=
  ∃ M > 0, ∀ n, a n > -M
