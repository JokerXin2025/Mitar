import Lean2TeX.Basic

def Rule_Succ : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``Nat.succ 1 then
    let n ← expr_rec expr.getAppArgs[0]! Basic
    return s!"{n}+1"
  return none

def Rule_Add : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``HAdd.hAdd 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! Basic
    let B ← expr_rec args[5]! Basic
    return s!"{A}+{B}"
  return none

def Rule_Sub : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``HSub.hSub 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! Basic
    let B ← expr_rec args[5]! Basic
    return s!"{A}-{B}"
  return none

def Rule_Mul : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``HMul.hMul 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! Basic
    let B ← expr_rec args[5]! Basic
    return s!"{A}\\cdot {B}"
  return none

def Rule_Div : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``HDiv.hDiv 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! Basic
    let B ← expr_rec args[5]! Basic
    return s!"\\frac{"{"}{A}{"}"}{"{"}{B}{"}"}"
  return none

def Rule_Pow : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``HPow.hPow 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! Basic
    let B ← expr_rec args[5]! Basic
    return s!"{A}^{"{"}{B}{"}"}"
  return none

def Rule_Neg : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``Neg.neg 3 then
    let X ← expr_rec expr.getAppArgs[2]! Basic
    return s!"-{X}"
  return none

def Rule_Inv : Rule := fun expr expr_rec => do
  if expr.isAppOfArity ``Inv.inv 3 then
    let X ← expr_rec expr.getAppArgs[2]! Basic
    return s!"{X}^{"{"}-1{"}"}"
  return none

def Rule_Abs : Rule := fun expr expr_rec => do
  if expr.isAppOfArity `abs 4 then
    let X ← expr_rec expr.getAppArgs[3]! Basic
    return s!"\\left|{X}\\right|"
  return none
