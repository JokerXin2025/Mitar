import «Calculus@Mitar».Basic


/- # 邻域 Neighborhood -/

--  开邻域 | Open Neighborhood
--  闭邻域 | Close Neighborhood


/- # 函数 Function -/

--  函数 | Function
abbrev Function := ℝ → ℝ


/- # 函数有界性 Boundedness of Function -/

--  有界 | Bounded
def FuncBounded (f : Function) : Prop :=
  ∃ M > 0, ∀ x, |f x| < M

--  局部有界 | Locally Bounded
def FuncLocallyBounded (f : Function) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∃ M > 0, ∀ x, |x - x₀| ∈ Set.Ioo 0 δ → |f x| < M

--  有上界 | Upper-Bounded
def FuncUpperBounded (f : Function) : Prop :=
  ∃ M > 0, ∀ x, f x < M

--  有下界 | Lower-Bounded
def FuncLowerBounded (f : Function) : Prop :=
  ∃ M > 0, ∀ x, f x > -M
