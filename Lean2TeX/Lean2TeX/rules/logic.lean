import Lean2TeX.Basic

def Rule_And : Rule := fun e rec => do
  if e.isAppOfArity `And 2 then
    let args := e.getAppArgs
    let A ← rec args[0]!
    let B ← rec args[1]!
    return some s!"{A}\\land {B}"
  return none

def Rule_Or : Rule := fun e rec => do
  if e.isAppOfArity `Or 2 then
    let args := e.getAppArgs
    let A ← rec args[0]!
    let B ← rec args[1]!
    return some s!"{A}\\lor {B}"
  return none

def Rule_Iff : Rule := fun e rec => do
  if e.isAppOfArity `Iff 2 then
    let args := e.getAppArgs
    let A ← rec args[0]!
    let B ← rec args[1]!
    return some s!"{A}\\leftrightarrow {B}"
  return none

def Rule_Not : Rule := fun e rec => do
  if e.isAppOfArity `Not 1 then
    let A ← rec e.getAppArgs[0]!
    return some s!"\\neg {A}"
  return none
