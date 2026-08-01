import Lean2TeX.Prelude
import Lean2TeX.Utils

open Lean2TeX
open Lean.Meta (forallTelescope)


def Rule_False_Word : Rule := fun expr _ _ _ => do
  if expr.isConstOf ``False then
    return (s!"矛盾", NodeType.Text)
  return none

def Rule_And_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``And 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .any .Text styles fvars
    let B ← expr_rec args[1]! .any .Text styles fvars
    return (s!"{A}且{B}", NodeType.Text)
  return none

def Rule_Or_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Or 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .any .Text styles fvars
    let B ← expr_rec args[1]! .any .Text styles fvars
    return (s!"{A}或{B}", NodeType.Text)
  return none

def Rule_Iff_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Iff 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .any .Text styles fvars
    let B ← expr_rec args[1]! .any .Text styles fvars
    return (s!"{A}当且仅当{B}", NodeType.Text)
  return none

def Rule_Not_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Not 1 then
    let arg := expr.getAppArgs[0]!
    let A ← expr_rec arg .any .Text styles fvars
    if arg.isAppOfArity ``Exists 2 then
      return (s!"不{A}", NodeType.Text)
    else
      return (s!"命题{A}不成立", NodeType.Text)
  return none

def Rule_Implies_Symbol : Rule := fun expr expr_rec styles fvars => do
  match expr with
  | .forallE _ binder body _ => do
      if expr.isArrow then
        let XXX ← expr_rec binder .left .Implies styles fvars
        let YYY ← expr_rec body .right .Implies styles fvars
        return (s!"{XXX}\\implies {YYY}", NodeType.Implies)
      else
        return none
  | _ => return none

def Rule_Forall_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isForall then
    if !expr.isArrow then
      let res ← forallTelescope expr fun _fvars body => do
        let XXX ← expr_rec body .any .Text styles fvars
        match _fvars.size with
        | 1 =>
          let x ← expr_rec _fvars[0]! .left .Rel styles fvars
          let A ← expr_rec (← inferType _fvars[0]!) .right .Rel styles fvars
          return s!"{XXX}对一切 ${x}\\in {A}$ 成立"
        | 2 =>
          let typeExpr1 := ← inferType _fvars[0]!
          let typeExpr2 := ← inferType _fvars[1]!
          match ← isProp typeExpr1, ← isProp typeExpr2 with
          | true, true =>
            let A ← expr_rec typeExpr1 .any .Text styles fvars
            let B ← expr_rec typeExpr2 .any .Text styles fvars
            return s!"若{A}且{B}, 则{XXX}"
          | true, false => return ""
          | false, true =>
            let x ← expr_rec _fvars[0]! .left .Rel styles fvars
            let A ← expr_rec typeExpr1 .right .Rel styles fvars
            let B ← expr_rec typeExpr2 .any .Text styles fvars
            return s!"对任意满足{B}的 ${x}\\in {A}$ 有{XXX}"
          | false, false =>
            let x ← expr_rec _fvars[0]! .left .Rel styles fvars
            let y ← expr_rec _fvars[1]! .left .Rel styles fvars
            let A ← expr_rec typeExpr1 .right .Rel styles fvars
            let B ← expr_rec typeExpr2 .right .Rel styles fvars
            return s!"{XXX}对一切 ${x}\\in {A}$ 和 ${y}\\in {B}$ 成立"
        | _ =>
          let mut xAyB_array := #[]
          for fvar in _fvars do
            let x ← expr_rec fvar .left .Rel styles fvars
            let A ← expr_rec (← inferType fvar) .right .Rel styles fvars
            xAyB_array := xAyB_array.push s!"{x}\\in {A}"
          let xAyB := "\\,,\\,".intercalate xAyB_array.toList
          return s!"对任意 ${xAyB}$ 有: {XXX}"
      return (res, NodeType.Text)
    else
      return none
  else
    return none

def Rule_Exists_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Exists 2 then
    let res ← existsTelescope expr fun _fvars safeBody => do
      let mut varList := #[]
      for fvar in _fvars do
        let x ← expr_rec fvar .left .Rel styles fvars
        let A ← expr_rec (← inferType fvar) .right .Rel styles fvars
        varList := varList.push s!"{x}\\in{A}"
      let xAyB := "\\,,\\,".intercalate varList.toList
      let XXX ← expr_rec safeBody .any .Text styles fvars
      return s!"存在 ${xAyB}$ 使得{XXX}"
    return (res, NodeType.Text)
  return none
