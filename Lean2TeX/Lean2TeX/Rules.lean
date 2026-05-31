import Lean2TeX.Basic
import Lean2TeX.Utils
import Lean2TeX.Rules.Logic
import Lean2TeX.Rules.Arithmetic
import Lean2TeX.Rules.Relation
import Lean2TeX.Rules.NumberSystem
import Lean2TeX.Rules.Calculus

open Lean2TeX
open Lean.Meta (lambdaTelescope)

def MetaRule_Lambda : MetaRule := fun expr parent style expr_rec => do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _ body =>
      expr_rec body parent style
    return (res, parent)
  return none

def MetaRule_OfNat : MetaRule := fun expr parent style expr_rec => do
  if expr.isAppOfArity' ``OfNat.ofNat 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[1]! parent style, parent)
  return none

def MetaRule_Cast : MetaRule := fun expr parent style expr_rec => do
  if expr.isAppOfArity' ``Nat.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent style, parent)
  else if expr.isAppOfArity' ``Int.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent style, parent)
  return none

def PresetMetaRules : List MetaRule := [
  (MetaRule_Lambda),
  (MetaRule_OfNat),
  (MetaRule_Cast)
]

def PresetRules : List (Rule × TeXStyle) := [
  (Rule_False_Word, .Basic), (Rule_False_Word, .Word),
  (Rule_And_Word, .Basic), (Rule_And_Word, .Word),
  (Rule_Or_Word, .Basic), (Rule_Or_Word, .Word),
  (Rule_Iff_Word, .Basic), (Rule_Iff_Word, .Word),
  (Rule_Not_Word, .Basic), (Rule_Not_Word, .Word),
  (Rule_Implies_Symbol, .Basic), (Rule_Implies_Symbol, .Symbol),
  (Rule_Forall_Word, .Basic), (Rule_Forall_Word, .Word),
  (Rule_Exists_Word, .Basic), (Rule_Exists_Word, .Word),
  (Rule_Succ, .Basic),
  (Rule_Add, .Basic),
  (Rule_Sub, .Basic),
  (Rule_Mul, .Basic),
  (Rule_Div, .Basic),
  (Rule_Pow, .Basic),
  (Rule_Neg, .Basic),
  (Rule_Inv, .Basic),
  (Rule_Abs, .Basic),
  (Rule_Eq, .Basic),
  (Rule_NotEq, .Basic),
  (Rule_Less, .Basic),
  (Rule_LessEqual, .Basic),
  (Rule_Greater, .Basic),
  (Rule_GreaterEqual, .Basic),
  (Rule_Mathbb_Nat, .Basic), (Rule_Mathbb_Nat, .Mathbb),
  (Rule_Mathbb_Real, .Basic), (Rule_Mathbb_Real, .Mathbb),
  (Rule_Mathbf_Nat, .Mathbf),
  (Rule_Mathbf_Real, .Mathbf),
  (Rule_NumSeq, .Basic),
  (Rule_Func, .Basic)
]
