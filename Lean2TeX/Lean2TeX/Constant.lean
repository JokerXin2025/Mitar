import Lean2TeX.Utils

open Lean2TeX
open Lean (getConstInfo)
open Lean.Meta (getEqnsFor?)
open Lean.ConstantInfo

namespace Lean2TeX


def Expr.isComplexDef (expr : Expr) : Bool :=
  Option.isSome <| expr.find? fun
  | .const n _ =>
    let s := n.toString
    s.contains "brecOn" || s.contains "casesOn" || s.contains "recOn"
  | _ => false

def Lean.Expr.getConstDef : Expr → ExprRecFunc → NodeRole → NodeType → List DisplayType → List (FVarId × String)
  → MetaM (Option NodeInfo) := fun expr expr_rec role parent styles fvars => do
  /- Move `.Def` from the DisplayType list -/
  let styles := styles.erase .Def
  match ← getConstInfo expr.constName! with
  /- __Expression or Equations__ -/
  | defnInfo defn =>
    if Expr.isComplexDef defn.value then
      if let some eqns ← getEqnsFor? expr.constName! then
        let mut output_array := #[]
        for eqnName in eqns do
          let next ← expr_rec (← getConstInfo eqnName).type .any/- !!! -/ .MultiLine styles fvars
          output_array := output_array.push next
        let output := "\\\\".intercalate output_array.toList
        let output' := s!"$$\\begin{"{"}cases{"}"}{output}\\end{"{"}cases{"}"}$$"
        return (output', NodeType.Text)
      else
        return none
    else
      return (← expr_rec defn.value role parent styles fvars, parent)
  /- __Theorem (or Lemma)__ -/
  | thmInfo thm =>
    return (← expr_rec thm.type role parent styles fvars, parent)
  /- __Axiom__ -/
  | axiomInfo _axiom =>
    return (← expr_rec _axiom.type role parent styles fvars, parent)
  /- __Inductive__ -/
  | inductInfo _ =>
    return none
  /- __Constructor__ -/
  | ctorInfo _ =>
    return none
  /- __Recursor / Eliminator__ -/
  | recInfo _ =>
    return none
  /- __Opaque__ -/
  | opaqueInfo _ =>
    return none
  /- __Quotient Info__ -/
  | quotInfo _ =>
    return none

end Lean2TeX
