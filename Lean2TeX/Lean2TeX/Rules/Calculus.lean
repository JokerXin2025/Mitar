import Lean2TeX.Defs

open Lean2TeX

def Rule_NumSeq : Rule := fun expr expr_rec styles fvars => do
  if expr.isApp then
    if (← inferType expr.appArg!).isConstOf ``Nat then
      let a ← expr_rec expr.appFn! .BySubscript ([.Plain] ++ styles) fvars
      let n ← expr_rec expr.appArg! .Subscript styles fvars
      return (s!"{a}_{"{"}{n}{"}"}", NodeType.Subscript)
  return none

def Rule_Func : Rule := fun expr expr_rec styles fvars => do
  if expr.isApp then
    if (← inferType expr.appArg!).isConstOf `Real then
      let f ← expr_rec expr.appFn! .BracApp ([.Plain] ++ styles) fvars
      let x ← expr_rec expr.appArg! .BracApp styles fvars
      return (s!"{f}({x})", NodeType.BracApp)
  return none
