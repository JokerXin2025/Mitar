import Lean2TeX.Basic

def Rule_Eq : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``Eq 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! Basic
    let B ← expr_rec args[2]! Basic
    return s!"{A}={B}"
  return none

def Rule_NotEq : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``Ne 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! Basic
    let B ← expr_rec args[2]! Basic
    return s!"{A}\\ne {B}"
  return none

def Rule_Less : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``LT.lt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! Basic
    let B ← expr_rec args[3]! Basic
    return s!"{A}<{B}"
  return none

def Rule_LessEqual : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``LE.le 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! Basic
    let B ← expr_rec args[3]! Basic
    return s!"{A}\\leq {B}"
  return none

def Rule_Greater : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``GT.gt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! Basic
    let B ← expr_rec args[3]! Basic
    return s!"{A}>{B}"
  return none

def Rule_GreaterEqual : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``GE.ge 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! Basic
    let B ← expr_rec args[3]! Basic
    return s!"{A}\\geq {B}"
  return none
