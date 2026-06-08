import Lean2TeX.Basic

open Lean2TeX

def Rule_NumSeq : Rule := fun expr expr_rec => do
  if expr.consumeMData.isApp then
    if (← inferType expr.appArg!').isConstOf ``Nat then
      let a ← expr_rec expr.appFn!' .Subscript .Plain
      let n ← expr_rec expr.appArg!' .Subscript .Basic
      return (s!"{a}_{"{"}{n}{"}"}", OperNode.Subscript)
  return none

def Rule_Func : Rule := fun expr expr_rec => do
  if expr.consumeMData.isApp then
    if (← inferType expr.appArg!').isConstOf `Real then
      let f ← expr_rec expr.appFn!' .BracApp .Plain
      let x ← expr_rec expr.appArg!' .BracApp .Basic
      return (s!"{f}({x})", OperNode.BracApp)
  return none
