import Lean2TeX.Register
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Aesop.Frontend.Command

/- Notations from Mathlib4 -/
export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici subset_univ)
export Real (exp log sin cos tan cot sinh cosh tanh arcsin arccos)
export Finset (range)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n

/- Constants from Mathlib4 -/
noncomputable section
def e := Real.exp 1
def π := Real.pi
end

declare_aesop_rule_sets [AutoEquation]
declare_aesop_rule_sets [LimitBasic]
declare_aesop_rule_sets [LimitEquivalent]
declare_aesop_rule_sets [FunctionContinuity]
declare_aesop_rule_sets [AutoLimit]
declare_aesop_rule_sets [Derivative]
