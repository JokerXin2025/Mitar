import Lean2TeX.rules.logic
import Lean2TeX.rules.arithmetic
import Lean2TeX.rules.relation
import Lean2TeX.rules.calculus

def Process_lambda : Rule := fun e rec => do
  if e.isLambda then
    let res ← Lean.Meta.lambdaTelescope e fun _ body => do
      rec body
    return some res
  return none

def Rule_OfNat : Rule := fun e rec => do
  if e.isAppOfArity ``OfNat.ofNat 3 then
    let args := e.getAppArgs
    let num ← rec args[1]!
    return some num
  return none

def Rules : List Rule := [
  Process_lambda,
  Rule_OfNat,
  Rule_Not,
  Rule_And,
  Rule_Or,
  Rule_Iff,
  Rule_Succ,
  Rule_Add,
  Rule_Sub,
  Rule_Mul,
  Rule_Div,
  Rule_Pow,
  Rule_Neg,
  Rule_Inv,
  Rule_Abs,
  Rule_Eq,
  Rule_NotEq,
  Rule_Less,
  Rule_LessEqual,
  Rule_Great,
  Rule_GreatEqual,
  Rule_NumSeq,
  Rule_Func
]
