import Lean2TeX.Defs

open Lean2TeX

def Rule_Succ : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Nat.succ 1 then
    let args := expr.getAppArgs
    let n ← expr_rec args[0]! .Add styles fvars
    return (s!"{n}+1", NodeType.Add)
  return none

def Rule_Add : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HAdd.hAdd 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Add styles fvars
    let B ← expr_rec args[5]! .Add styles fvars
    return (s!"{A}+{B}", NodeType.Add)
  return none

def Rule_Sub : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HSub.hSub 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Add styles fvars
    let B ← expr_rec args[5]! .Add styles fvars
    return (s!"{A}-{B}", NodeType.Add)
  return none

def Rule_Mul : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HMul.hMul 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Mul styles fvars
    let B ← expr_rec args[5]! .Mul styles fvars
    return (s!"{A}\\cdot {B}", NodeType.Mul)
  return none

def Rule_Div : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HDiv.hDiv 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Frac styles fvars
    let B ← expr_rec args[5]! .Frac styles fvars
    return (s!"\\frac{"{"}{A}{"}"}{"{"}{B}{"}"}", NodeType.Frac)
  return none

def Rule_Pow : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HPow.hPow 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .BySupscript styles fvars
    let B ← expr_rec args[5]! .Supscript styles fvars
    return (s!"{A}^{"{"}{B}{"}"}", NodeType.Supscript)
  return none

def Rule_Neg : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Neg.neg 3 then
    let args := expr.getAppArgs
    let X ← expr_rec args[2]! .Minus styles fvars
    return (s!"-{X}", NodeType.Minus)
  return none

def Rule_Inv : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Inv.inv 3 then
    let args := expr.getAppArgs
    let X ← expr_rec args[2]! .BySupscript styles fvars
    return (s!"{X}^{"{"}-1{"}"}", NodeType.Supscript)
  return none

def Rule_Abs : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity `abs 4 then
    let args := expr.getAppArgs
    let X ← expr_rec args[3]! .Abs styles fvars
    return (s!"\\left|{X}\\right|", NodeType.Abs)
  return none
