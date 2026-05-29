import Lean2TeX.Basic

def Rule_Word_And : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``Int 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    let B ← expr_rec args[1]! .Text .Basic
    return (s!"{A}且{B}", OperNode.Text)
  return none

def Rule_Word_Or : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `Or 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    let B ← expr_rec args[1]! .Text .Basic
    return (s!"{A}或{B}", OperNode.Text)
  return none

def Rule_Word_Iff : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `Iff 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    let B ← expr_rec args[1]! .Text .Basic
    return (s!"{A}当且仅当{B}", OperNode.Text)
  return none

def Rule_Word_Not : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `Not 1 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text .Basic
    return (s!"命题{A}不成立", OperNode.Text)
  return none
