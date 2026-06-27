import Lean2TeX.Register
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Aesop

/- Notations from Mathlib4 -/
export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici)
export Finset (range)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n

/- Constants from Mathlib4 -/
noncomputable section
def e := Real.exp 1
def π := Real.pi
end

declare_aesop_rule_sets [LimitSimplify]
declare_aesop_rule_sets [LimitEquivalent]
declare_aesop_rule_sets [Derivative]
