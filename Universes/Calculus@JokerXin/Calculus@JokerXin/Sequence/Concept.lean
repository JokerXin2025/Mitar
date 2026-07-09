import «Calculus@JokerXin».Sequence.Defs


/- ## 数列有界性 Boundedness of Sequence -/

/-- ### 有界
    ### Bounded -/
def SeqBounded (A : Sequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, |A.map n| < M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, |A.map n| < M

/-- ### 有上界
    ### Upper-Bounded -/
def SeqUpperBounded (A : Sequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, A.map n < M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, A.map n < M

/-- ### 有下界
    ### Lower-Bounded -/
def SeqLowerBounded (A : Sequence) : Prop :=
  match A.final with
  | some final! =>
    ∃ M > 0, ∀ n ∈ Ico A.init final!, A.map n > -M
  | none =>
    ∃ M > 0, ∀ n ∈ Ici A.init, A.map n > -M
