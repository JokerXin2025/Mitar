import Lean2TeX.Defs

open Lean2TeX

def Rule_Eq : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Eq 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! .Rel styles fvars
    let B ← expr_rec args[2]! .Rel styles fvars
    return (s!"{A}={B}", NodeType.Rel)
  return none

def Rule_NotEq : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Ne 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! .Rel styles fvars
    let B ← expr_rec args[2]! .Rel styles fvars
    return (s!"{A}\\ne {B}", NodeType.Rel)
  return none

def Rule_Less : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``LT.lt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}<{B}", NodeType.Rel)
  return none

def Rule_LessEqual : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``LE.le 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}\\leqslant {B}", NodeType.Rel)
  return none

def Rule_Greater : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``GT.gt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}>{B}", NodeType.Rel)
  return none

def Rule_GreaterEqual : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``GE.ge 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}\\geqslant {B}", NodeType.Rel)
  return none
