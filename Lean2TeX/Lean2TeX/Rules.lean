import Lean2TeX.Basic
import Lean2TeX.Utils
import Lean2TeX.Rules.Logic
import Lean2TeX.Rules.Arithmetic
import Lean2TeX.Rules.Relation
import Lean2TeX.Rules.NumberSystem
import Lean2TeX.Rules.Calculus

export Lean.Meta (
  inferType
  lambdaTelescope
  forallTelescope
)
export Lean2TeX.Lean.Meta (existsTelescope)

def MetaRule_Lambda : MetaRule := fun expr parent style expr_rec => do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _ body =>
      expr_rec body parent style
    return (res, parent)
  return none

def Rule_Implies_Symbol : Rule := fun expr expr_rec => do
  match expr with
  | .forallE _ binder body _ => do
      if expr.isArrow then
        let XXX ← expr_rec binder .Implies .Basic
        let YYY ← expr_rec body .Implies .Basic
        return (s!"{XXX}\\implies{YYY}", OperNode.Implies)
      else
        return none
  | _ => return none

def Rule_Forall_Word : Rule := fun expr expr_rec => do
  if expr.isForall then
    if !expr.isArrow then
      let res ← forallTelescope expr fun fvars body => do
        let XXX ← expr_rec body .Text .Basic
        match fvars.size with
        | 1 =>
          let x ← expr_rec fvars[0]! .Rel .Basic
          let A ← expr_rec (← inferType fvars[0]!) .Rel .Basic
          return s!"{XXX}对一切 ${x}\\in{A}$ 成立"
        | 2 =>
          let x ← expr_rec fvars[0]! .Rel .Basic
          let A ← expr_rec (← inferType fvars[0]!) .Rel .Basic
          let y ← expr_rec fvars[1]! .Rel .Basic
          let B ← expr_rec (← inferType fvars[1]!) .Rel .Basic
          return s!"{XXX}对一切 ${x}\\in{A}$ 和 ${y}\\in{B}$ 成立"
        | _ =>
          let mut xAyB_array := #[]
          for fvar in fvars do
            let x ← expr_rec fvar .Rel .Basic
            let A ← expr_rec (← inferType fvar) .Rel .Basic
            xAyB_array := xAyB_array.push s!"{x}\\in{A}"
          let xAyB := "\\,,\\,".intercalate xAyB_array.toList
          return s!"对任意 ${xAyB}$ 有: {XXX}"
      return (res, OperNode.Text)
    else
      return none
  else
    return none

def Rule_Exists_Word : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``Exists 2 then
    let res ← existsTelescope expr fun fvars safeBody => do
      let mut varList := #[]
      for fvar in fvars do
        let x ← expr_rec fvar .Rel .Basic
        let A ← expr_rec (← inferType fvar) .Rel .Basic
        varList := varList.push s!"{x}\\in{A}"
      let xAyB := "\\,,\\,".intercalate varList.toList
      let XXX ← expr_rec safeBody .Rel .Basic
      return s!"存在 ${xAyB}$ 使得 {XXX}"
    return (res, OperNode.Text)
  return none

def Rule_OfNat : MetaRule := fun expr parent style expr_rec => do
  if expr.isAppOfArity' ``OfNat.ofNat 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[1]! parent style, parent)
  return none

def Rule_Nat_Cast : MetaRule := fun expr parent style expr_rec => do
  if expr.isAppOfArity' ``Nat.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent style, parent)
  if expr.isAppOfArity' ``Int.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent style, parent)
  return none

def PresetMetaRules : List MetaRule := [
  (MetaRule_Lambda),
  (Rule_OfNat),
  (Rule_Nat_Cast)
]

def PresetRules : List (Rule × TeXStyle) := [
  (Rule_Word_And, .Basic), (Rule_Word_And, .Word),
  (Rule_Word_Or, .Basic), (Rule_Word_Or, .Word),
  (Rule_Word_Iff, .Basic), (Rule_Word_Iff, .Word),
  (Rule_Word_Not, .Basic), (Rule_Word_Not, .Word),
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
