import Lean2TeX.Basic

def Rule_Eq : Rule := fun e rec => do
  if e.isAppOfArity ``Eq 3 then
    let args := e.getAppArgs
    let A ← rec args[1]!
    let B ← rec args[2]!
    return some s! "{A}={B}"
  return none

def Rule_NotEq : Rule := fun e rec => do
  if e.isAppOfArity ``Ne 3 then
    let args := e.getAppArgs
    let A ← rec args[1]!
    let B ← rec args[2]!
    return some s! "{A}\\ne {B}"
  return none

def Rule_Less : Rule := fun e rec => do
  if e.isAppOfArity ``LT.lt 4 then
    let args := e.getAppArgs
    let A ← rec args[2]!
    let B ← rec args[3]!
    return some s! "{A}<{B}"
  return none

def Rule_LessEqual : Rule := fun e rec => do
  if e.isAppOfArity ``LE.le 4 then
    let args := e.getAppArgs
    let A ← rec args[2]!
    let B ← rec args[3]!
    return some s! "{A}\\leq {B}"
  return none

def Rule_Great : Rule := fun e rec => do
  if e.isAppOfArity ``GT.gt 4 then
    let args := e.getAppArgs
    let A ← rec args[2]!
    let B ← rec args[3]!
    return some s! "{A}>{B}"
  return none

def Rule_GreatEqual : Rule := fun e rec => do
  if e.isAppOfArity ``GE.ge 4 then
    let args := e.getAppArgs
    let A ← rec args[2]!
    let B ← rec args[3]!
    return some s! "{A}\\geq {B}"
  return none
