import Lean2TeX.Basic

def Rule_NumSeq : Rule := fun expr expr_rec => do
  if expr.isApp then
    let a ← expr_rec expr.appFn! Plain
    let n ← expr_rec expr.appArg! Basic
    if (← Meta.inferType expr.appArg!').isConstOf ``Nat then
      return s!"{a}_{"{"}{n}{"}"}"
  return none

def Rule_Func : Rule := fun expr expr_rec => do
  if expr.isApp then
    let f ← expr_rec expr.appFn! Plain
    let x ← expr_rec expr.appArg! Basic
    if (← Meta.inferType expr.appArg!').isConstOf ``Real then
      return s!"{f}({x})"
  return none
