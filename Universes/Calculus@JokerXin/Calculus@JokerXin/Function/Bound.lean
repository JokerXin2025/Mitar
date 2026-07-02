import «Calculus@JokerXin».Function.Defs


/- # 函数有界性 Boundedness of Function -/

/-- ### 有界
    ### Bounded -/
def Bounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, |F.map x| < M

/-- ### 有上界
    ### Upper-Bounded -/
def UpperBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x < M

/-- ### 有下界
    ### Lower-Bounded -/
def LowerBounded (F : Function) : Prop :=
  ∃ M > 0, ∀ x ∈ F.domain, F.map x > -M
