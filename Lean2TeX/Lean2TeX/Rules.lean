import Lean2TeX.Defs
import Lean2TeX.Utils
import Lean2TeX.Register
import Lean2TeX.Variable
import Lean2TeX.Rules.Logic
import Lean2TeX.Rules.Arithmetic
import Lean2TeX.Rules.Relation
import Lean2TeX.Rules.NumberSystem
import Lean2TeX.Rules.Calculus

open Lean2TeX
open Lean (getEnv)
open Lean.Meta (lambdaTelescope)

def MetaRule_Lambda : MetaRule := fun expr expr_rec parent styles fvars => do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _ body =>
      expr_rec body parent styles fvars
    return (res, parent)
  return none

def MetaRule_Lambda' : Expr → ExprRecFunc → NodeType → List DisplayType → List (FVarId × String) → Array String → MetaM (Option String) := fun expr expr_rec parent styles fvars fvar_strings => do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _fvars body =>
      expr_rec body parent styles (fvars.toArray ++ (_fvars.map (fun expr => expr.fvarId!)).zip fvar_strings).toList
    return res
  return none  -- change to `""` ?

def MetaRule_OfNat : MetaRule := fun expr expr_rec parent styles fvars => do
  if expr.isAppOfArity' ``OfNat.ofNat 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[1]! parent styles fvars, parent)
  return none

def MetaRule_Cast : MetaRule := fun expr expr_rec parent styles fvars => do
  if expr.isAppOfArity' ``Nat.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent styles fvars, parent)
  else if expr.isAppOfArity' ``Int.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent styles fvars, parent)
  return none

def Rule_Generic : Rule := fun expr expr_rec styles fvars => do
  let fn := expr.getAppFn
  match fn with
  | .const declName _ =>
    let env ← getEnv
    if let some templateData := Templates.find? env declName then
      let args := expr.getAppArgs
      let targetDisplay := templateData.config.TargetDisplay
      let argsDisplay := templateData.config.ArgsDisplay.toArray
      let argsContextNode := templateData.config.ArgsContextNode.toArray
      let mut evaledArgs := #[]
      let mut (res, fvar_list) ← processPlaceholders templateData.template
      let mut n := 0
      for arg in args do
        let argDisplay := (argsDisplay[n]?.getD []) ++ styles
        let argContextNode := argsContextNode[n]?.getD templateData.node
        if let some fvar_info? := fvar_list[n+1]? then
          if let some (type, index) := fvar_info? then
            if let some res' ← MetaRule_Lambda' arg.consumeMData expr_rec argContextNode argDisplay fvars #[s!"{type}{index+1}"] then
              evaledArgs := evaledArgs.push res'
            else
              let arg ← expr_rec arg argContextNode argDisplay fvars
              evaledArgs := evaledArgs.push arg
            releaseVar (type, index)
        else
          let arg ← expr_rec arg argContextNode argDisplay fvars
          evaledArgs := evaledArgs.push arg
        n := n + 1
      for i in [0:args.size] do
        res := res.replace s!"@{i+1}" evaledArgs[i]!
      return some (res, templateData.node)
    return none
  | _ => return none

def PresetMetaRules : List MetaRule := [
  (MetaRule_Lambda),
  (MetaRule_OfNat),
  (MetaRule_Cast)
]

def PresetRules : List (Rule × DisplayType) := [
  (Rule_Generic, .Basic),
  (Rule_False_Word, .Basic), (Rule_False_Word, .Word),
  (Rule_And_Word, .Basic), (Rule_And_Word, .Word),
  (Rule_Or_Word, .Basic), (Rule_Or_Word, .Word),
  (Rule_Iff_Word, .Basic), (Rule_Iff_Word, .Word),
  (Rule_Not_Word, .Basic), (Rule_Not_Word, .Word),
  (Rule_Implies_Symbol, .Basic), (Rule_Implies_Symbol, .Symbol),
  (Rule_Forall_Word, .Basic), (Rule_Forall_Word, .Word),
  (Rule_Exists_Word, .Basic), (Rule_Exists_Word, .Word),
  (Rule_Succ, .Basic),
  (Rule_Add, .Basic),
  (Rule_Sub, .Basic),
  (Rule_Mul, .Basic),
  (Rule_Div, .Basic),
  (Rule_Pow, .Basic),
  (Rule_Neg, .Basic),
  (Rule_Inv, .Basic),
  (Rule_Abs, .Basic),
  (Rule_Eq, .Basic),
  (Rule_NotEq, .Basic),
  (Rule_Less, .Basic),
  (Rule_LessEqual, .Basic),
  (Rule_Greater, .Basic),
  (Rule_GreaterEqual, .Basic),
  (Rule_Mathbb_Nat, .Basic), (Rule_Mathbb_Nat, .Mathbb),
  (Rule_Mathbb_Real, .Basic), (Rule_Mathbb_Real, .Mathbb),
  (Rule_Mathbf_Nat, .Mathbf),
  (Rule_Mathbf_Real, .Mathbf),
  (Rule_NumSeq, .Basic),
  (Rule_Func, .Basic)
]
