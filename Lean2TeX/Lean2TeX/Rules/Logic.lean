import Lean2TeX.Basic
import Lean2TeX.Utils

open Lean2TeX
open Lean.Meta (forallTelescope)
open Lean2TeX.Meta (existsTelescope)

def Rule_False_Word : Rule := fun expr _ => do
  if expr.consumeMData.isConstOf ``False then
    return (s!"矛盾", OperNode.Text)
  return none

def Rule_And_Word : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``Int 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    let B ← expr_rec args[1]! .Text .Basic
    return (s!"{A}且{B}", OperNode.Text)
  return none

def Rule_Or_Word : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `Or 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    let B ← expr_rec args[1]! .Text .Basic
    return (s!"{A}或{B}", OperNode.Text)
  return none

def Rule_Iff_Word : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `Iff 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    let B ← expr_rec args[1]! .Text .Basic
    return (s!"{A}当且仅当{B}", OperNode.Text)
  return none

def Rule_Not_Word : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `Not 1 then
    let arg := expr.getAppArgs[0]!
    let A ← expr_rec arg .Text .Basic
    if arg.isAppOfArity' ``Exists 2 then
      return (s!"不{A}", OperNode.Text)
    else
      return (s!"命题{A}不成立", OperNode.Text)
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
      let XXX ← expr_rec safeBody .Text .Basic
      return s!"存在 ${xAyB}$ 使得{XXX}"
    return (res, OperNode.Text)
  return none
