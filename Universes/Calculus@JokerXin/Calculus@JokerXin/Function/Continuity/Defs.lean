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

/-- ### 在某处左连续
    ### Left Continuous at Some Point -/
def isLeftContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  LeftLimit F x₀ (F.map x₀)

/-- ### 在某处右连续
    ### Right Continuous at Some Point -/
def isRightContinuousAt (F : Function) (x₀ : ℝ) : Prop :=
  RightLimit F x₀ (F.map x₀)

/-- ### 在闭区间上连续
    ### Continuous on the Closed Interval
    Similar to `isContinuousIn`, but continuity at the endpoints represents right
    continuity and left continuity respectively.
    - Before using it, please make sure that `l < r` -/
abbrev isContinuousInIcc (F : Function) (l r : ℝ) : Prop :=
  isContinuousIn F (Ioo l r)
  ∧ isRightContinuousAt F l
  ∧ isLeftContinuousAt F r


/- ## 函数连续性引理 Lemmas on Function Continuity -/

/-- ### 处处连续 ⇒ 在某处连续
    ### Continuous Everywhere ⇒ Continuous at Some Point -/
lemma isContinuous_implies_At {F : Function} {x₀ : ℝ}
    (h_cont : isContinuous F) (h_dom : x₀ ∈ F.domain)
  : isContinuousAt F x₀
:= h_cont x₀ h_dom

/-- ### 在区间上连续 ⇒ 在某处连续
    ### Continuous on the Interval ⇒ Continuous at Some Point -/
lemma isContinuousIn_implies_At {F : Function} {x₀ : ℝ} {I : Set ℝ}
    (h_cont : isContinuousIn F I) (h_dom : x₀ ∈ I)
  : isContinuousAt F x₀
:= h_cont x₀ h_dom

/-- ### 在某处连续 ⇒ 在某处左连续
    ### Continuous at Some Point ⇒ Left Continuous at Some Point -/
lemma isContinuousAt_implies_LeftAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : isLeftContinuousAt F x₀
:= FuncLimit.toLeft h_cont

/-- ### 在某处连续 ⇒ 在某处右连续
    ### Continuous at Some Point ⇒ Right Continuous at Some Point -/
lemma isContinuousAt_implies_RightAt {F : Function} {x₀ : ℝ}
    (h_cont : isContinuousAt F x₀)
  : isRightContinuousAt F x₀
:= FuncLimit.toRight h_cont
