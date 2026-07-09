import Lean2TeX.Register
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Aesop.Frontend.Command


/- # Notations from Mathlib4 -/

export Set (Ioo Icc Ioc Ico Iio Iic Ioi Ici mem_univ subset_univ)
export Real (exp sin cos tan cot sinh cosh tanh arcsin arccos arctan)
export Finset (range)
abbrev Iii : Set ℝ := Set.univ
notation:10000 n "!" => Nat.factorial n
noncomputable abbrev ln := Real.log


/- # Supplementary Definitions -/

noncomputable def e := Real.exp 1
noncomputable def π := Real.pi
noncomputable def sec := (fun x ↦ 1 / cos x)
noncomputable def csc := (fun x ↦ 1 / sin x)
noncomputable def coth := (fun x ↦ 1 / tanh x)
noncomputable def sech := (fun x ↦ 1 / cosh x)
noncomputable def csch := (fun x ↦ 1 / sinh x)
noncomputable def arccot := (fun x ↦ π / 2 - arctan x)
noncomputable def arcsec := (fun x ↦ arccos (1 / x))
noncomputable def arccsc := (fun x ↦ arcsin (1 / x))

macro "the" : term => `(some)
macro "directly" id:ident : term => `(fun _ ↦ $id)


/- # Declarations for Aesop -/

declare_aesop_rule_sets [InitializeExpr]
declare_aesop_rule_sets [ExprSimplify]

declare_aesop_rule_sets [AutoEquation]
declare_aesop_rule_sets [LimitInfinitesimal]
declare_aesop_rule_sets [LimitBasic]
declare_aesop_rule_sets [LimitEquivalent]
declare_aesop_rule_sets [Derivative]
