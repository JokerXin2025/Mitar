import Lean2TeX.Basic

def Rule_And : Rule := fun expr expr_rec => do
  if expr.isAppOfArity `And 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! Basic
    let B ← expr_rec args[1]! Basic
    return s!"{A}\\land {B}"
  return none

def Rule_Or : Rule := fun expr expr_rec => do
  if expr.isAppOfArity `Or 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! Basic
    let B ← expr_rec args[1]! Basic
    return s!"{A}\\lor {B}"
  return none

def Rule_Iff : Rule := fun expr expr_rec => do
  if expr.isAppOfArity `Iff 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! Basic
    let B ← expr_rec args[1]! Basic
    return s!"{A}\\leftrightarrow {B}"
  return none

def Rule_Not : Rule := fun expr expr_rec => do
  if expr.isAppOfArity `Not 1 then
    let A ← expr_rec expr.getAppArgs[0]! Basic
    return s!"\\neg {A}"
  return none
