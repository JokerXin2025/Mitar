import Lean2TeX.Prelude
import Lean2TeX.Attributes
import Lean2TeX.Variable
import Lean2TeX.Rules.Logic
import Lean2TeX.Rules.Operations
import Lean2TeX.Rules.Relations
import Lean2TeX.Rules.NumberSystem

open Lean2TeX
open Lean (getEnv)
open Lean.Meta (lambdaTelescope)

def processLambda_withFVars (expr : Expr)
                            (expr_rec : ExprRecFunc)
                            (parent : NodeType)
                            (role : NodeRole)
                            (styles : List DisplayType)
                            (fvars : List (FVarId × String))
                            (fvar_strings : Array String)
                            : MetaM (Option String) := do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _fvars body =>
      expr_rec body parent role styles (fvars.toArray ++ (_fvars.map (fun expr => expr.fvarId!)).zip fvar_strings).toList
    return res
  return none  -- maybe change to `""` ?

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
            if let some res' ← processLambda_withFVars arg.consumeMData expr_rec argContextNode .only argDisplay fvars #[s!"{type}{index+1}"] then
              evaledArgs := evaledArgs.push res'
            else
              let arg ← expr_rec arg argContextNode .only argDisplay fvars
              evaledArgs := evaledArgs.push arg
            releaseVar (type, index)
        else
          let arg ← expr_rec arg argContextNode .only argDisplay fvars
          evaledArgs := evaledArgs.push arg
        n := n + 1
      for i in [0:args.size] do
        res := res.replace s!"@{i+1}" evaledArgs[i]!
      return some (res, templateData.node)
    return none
  | _ => return none

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
  (Rule_Ne, .Basic),
  (Rule_LT, .Basic),
  (Rule_LE, .Basic),
  (Rule_GT, .Basic),
  (Rule_GE, .Basic),
  (Rule_Mathbb_Nat, .Basic), (Rule_Mathbb_Nat, .Mathbb),
  (Rule_Mathbb_Real, .Basic), (Rule_Mathbb_Real, .Mathbb),
  (Rule_Mathbf_Nat, .Mathbf),
  (Rule_Mathbf_Real, .Mathbf)
]
