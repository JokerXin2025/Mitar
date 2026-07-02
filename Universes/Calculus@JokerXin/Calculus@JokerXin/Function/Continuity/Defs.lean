import «Calculus@JokerXin».Limit.Defs


/- ## 函数连续性的定义 Definitions of Function Continuity -/

/-- ### 在某处连续
    ### Continuous at Some Point -/
def isContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  FuncLimit F x₀ (F.map x₀)

/-- ### 处处连续
    ### Continuous Everywhere -/
abbrev isContinuous (F : Function) : Prop :=
  ∀ x ∈ F.domain, isContinuousAt F x

/-- ### 在区间上连续
    ### Continuous on the Interval -/
abbrev isContinuousIn (F : Function) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, isContinuousAt F x


/- ## 函数连续性引理 Lemmas on Function Continuity -/

/-- ### 处处连续 ⇒ 在某处连续
    ### Continuous Everywhere ⇒ Continuous at Some Point -/
@[aesop unsafe 50% apply (rule_sets := [FunctionContinuity])]
lemma isContinuous_implies_At {F : Function} {x : ℝ}
    (h_cont : isContinuous F) (h_dom : x ∈ F.domain)
  : isContinuousAt F x
:= h_cont x h_dom

/-- ### 在区间上连续 ⇒ 在某处连续
    ### Continuous on the Interval ⇒ Continuous at Some Point -/
lemma isContinuousIn_implies_At {F : Function} {x : ℝ} {I : Set ℝ}
    (h_cont : isContinuousIn F I) (h_dom : x ∈ I)
  : isContinuousAt F x
:= h_cont x h_dom
