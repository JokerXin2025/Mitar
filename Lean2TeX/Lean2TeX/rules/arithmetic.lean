import Lean2TeX.Basic

def Rule_Succ : Rule := fun e rec => do
  if e.isAppOfArity ``Nat.succ 1 then
    let n ← rec e.getAppArgs[0]!
    return some s! "{n}+1"
  return none

def Rule_Add : Rule := fun e rec => do
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let args := e.getAppArgs
    let A ← rec args[4]!
    let B ← rec args[5]!
    return some s! "{A}+{B}"
  return none

def Rule_Sub : Rule := fun e rec => do
  if e.isAppOfArity ``HSub.hSub 6 then
    let args := e.getAppArgs
    let A ← rec args[4]!
    let B ← rec args[5]!
    return some s! "{A}-{B}"
  return none

def Rule_Mul : Rule := fun e rec => do
  if e.isAppOfArity ``HMul.hMul 6 then
    let args := e.getAppArgs
    let A ← rec args[4]!
    let B ← rec args[5]!
    return some s! "{A}\\cdot {B}"
  return none

def Rule_Div : Rule := fun e rec => do
  if e.isAppOfArity ``HDiv.hDiv 6 then
    let args := e.getAppArgs
    let A ← rec args[4]!
    let B ← rec args[5]!
    return some s! "\\frac{"{"}{A}{"}"}{"{"}{B}{"}"}"
  return none

def Rule_Pow : Rule := fun e rec => do
  if e.isAppOfArity ``HPow.hPow 6 then
    let args := e.getAppArgs
    let A ← rec args[4]!
    let B ← rec args[5]!
    return some s! "{A}^{"{"}{B}{"}"}"
  return none

def Rule_Neg : Rule := fun e rec => do
  if e.isAppOfArity ``Neg.neg 3 then
    let X ← rec e.getAppArgs[2]!
    return some s! "-{X}"
  return none

def Rule_Inv : Rule := fun e rec => do
  if e.isAppOfArity ``Inv.inv 3 then
    let X ← rec e.getAppArgs[2]!
    return some s! "{X}^{"{"}-1{"}"}"
  return none

def Rule_Abs : Rule := fun e rec => do
  if e.isAppOfArity `abs 4 then
    let X ← rec e.getAppArgs[3]!
    return some s! "\\left|{X}\\right|"
  return none
