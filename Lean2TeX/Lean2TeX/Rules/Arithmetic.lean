import Lean2TeX.Basic

open Lean2TeX

def Rule_Succ : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``Nat.succ 1 then
    let args := expr.getAppArgs'
    let n ← expr_rec args[0]! .Add .Basic
    return (s!"{n}+1", OperNode.Add)
  return none

def Rule_Add : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``HAdd.hAdd 6 then
    let args := expr.getAppArgs'
    let A ← expr_rec args[4]! .Add .Basic
    let B ← expr_rec args[5]! .Add .Basic
    return (s!"{A}+{B}", OperNode.Add)
  return none

def Rule_Sub : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``HSub.hSub 6 then
    let args := expr.getAppArgs'
    let A ← expr_rec args[4]! .Add .Basic
    let B ← expr_rec args[5]! .Add .Basic
    return (s!"{A}-{B}", OperNode.Add)
  return none

def Rule_Mul : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``HMul.hMul 6 then
    let args := expr.getAppArgs'
    let A ← expr_rec args[4]! .Mul .Basic
    let B ← expr_rec args[5]! .Mul .Basic
    return (s!"{A}\\cdot {B}", OperNode.Mul)
  return none

def Rule_Div : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``HDiv.hDiv 6 then
    let args := expr.getAppArgs'
    let A ← expr_rec args[4]! .Frac .Basic
    let B ← expr_rec args[5]! .Frac .Basic
    return (s!"\\frac{"{"}{A}{"}"}{"{"}{B}{"}"}", OperNode.Frac)
  return none

def Rule_Pow : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``HPow.hPow 6 then
    let args := expr.getAppArgs'
    let A ← expr_rec args[4]! .Supscript .Basic
    let B ← expr_rec args[5]! .Supscript .Basic
    return (s!"{A}^{"{"}{B}{"}"}", OperNode.Supscript)
  return none

def Rule_Neg : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``Neg.neg 3 then
    let args := expr.getAppArgs'
    let X ← expr_rec args[2]! .Minus .Basic
    return (s!"-{X}", OperNode.Minus)
  return none

def Rule_Inv : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' ``Inv.inv 3 then
    let args := expr.getAppArgs'
    let X ← expr_rec args[2]! .Supscript .Basic
    return (s!"{X}^{"{"}-1{"}"}", OperNode.Supscript)
  return none

def Rule_Abs : Rule := fun expr expr_rec => do
  if expr.isAppOfArity' `abs 4 then
    let args := expr.getAppArgs'
    let X ← expr_rec args[3]! .Abs .Basic
    return (s!"\\left|{X}\\right|", OperNode.Abs)
  return none
