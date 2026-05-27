import Lean2TeX.Basic
import Lean2TeX.Rules.Logic
import Lean2TeX.Rules.Arithmetic
import Lean2TeX.Rules.Relation
import Lean2TeX.Rules.NumberSystem
import Lean2TeX.Rules.Calculus

def Process_lambda : Rule := fun expr expr_rec => do
  if expr.isLambda then
    let res ← Lean.Meta.lambdaTelescope expr fun _ body =>
      expr_rec body Basic
    return some res
  return none

def Rule_OfNat : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``OfNat.ofNat 3 then
    let args := expr.getAppArgs
    let num ← expr_rec args[1]! Basic
    return some num
  return none

def Rules : List (Rule × TeXStyle) := [
  (Process_lambda, Basic),
  (Rule_OfNat, Basic),
  (Rule_Not, Basic),
  (Rule_And, Basic),
  (Rule_Or, Basic),
  (Rule_Iff, Basic),
  (Rule_Succ, Basic),
  (Rule_Add, Basic),
  (Rule_Sub, Basic),
  (Rule_Mul, Basic),
  (Rule_Div, Basic),
  (Rule_Pow, Basic),
  (Rule_Neg, Basic),
  (Rule_Inv, Basic),
  (Rule_Abs, Basic),
  (Rule_Eq, Basic),
  (Rule_NotEq, Basic),
  (Rule_Less, Basic),
  (Rule_LessEqual, Basic),
  (Rule_Greater, Basic),
  (Rule_GreaterEqual, Basic),
  (Rule_Mathbb_Nat, Basic),
  (Rule_Mathbb_Real, Basic),
  (Rule_Mathbb_Nat, Mathbb),
  (Rule_Mathbf_Nat, Mathbf),
  (Rule_Mathbb_Real, Mathbb),
  (Rule_Mathbf_Real, Mathbf),
  (Rule_NumSeq, Basic),
  (Rule_Func, Basic)
]
