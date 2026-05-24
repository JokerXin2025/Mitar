import Lean2TeX.Basic
import Mathlib.Data.Real.Basic

def Rule_NumSeq : Rule := fun e rec => do
  if e.isApp then
    let a ← rec e.appFn!
    let n ← rec e.appArg!
    if (← Meta.inferType e.appArg!').isConstOf ``Nat then
      return some s! "{a}_{"{"}{n}{"}"}"
  return none

def Rule_Func : Rule := fun e rec => do
  if e.isApp then
    let f ← rec e.appFn!
    let x ← rec e.appArg!
    if (← Meta.inferType e.appArg!').isConstOf ``Real then
      return some s! "{f}({x})"
  return none
