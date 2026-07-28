import Lean2TeX.Prelude

open Lean2TeX


def Rule_Eq : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Eq 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! .Rel .left styles fvars
    let B ← expr_rec args[2]! .Rel .right styles fvars
    return (s!"{A}={B}", NodeType.Rel)
  return none

def Rule_Ne : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Ne 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! .Rel .left styles fvars
    let B ← expr_rec args[2]! .Rel .right styles fvars
    return (s!"{A}\\ne {B}", NodeType.Rel)
  return none

def Rule_LT : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``LT.lt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel .left styles fvars
    let B ← expr_rec args[3]! .Rel .right styles fvars
    return (s!"{A}<{B}", NodeType.Rel)
  return none

def Rule_LE : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``LE.le 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel .left styles fvars
    let B ← expr_rec args[3]! .Rel .right styles fvars
    return (s!"{A}\\leqslant {B}", NodeType.Rel)
  return none

def Rule_GT : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``GT.gt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel .left styles fvars
    let B ← expr_rec args[3]! .Rel .right styles fvars
    return (s!"{A}>{B}", NodeType.Rel)
  return none

def Rule_GE : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``GE.ge 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel .left styles fvars
    let B ← expr_rec args[3]! .Rel .right styles fvars
    return (s!"{A}\\geqslant {B}", NodeType.Rel)
  return none
