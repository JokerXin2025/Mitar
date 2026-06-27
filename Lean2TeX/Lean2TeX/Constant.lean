import Lean2TeX.Defs
import Lean2TeX.Utils

open Lean2TeX
open Lean Meta ConstantInfo

namespace Lean2TeX

def Lean.Expr.getConstDef : MetaRule := fun expr expr_rec parent styles fvars => do
  /- Move `.Def` from the DisplayType list -/
  let styles := styles.erase .Def
  match ← getConstInfo expr.constName! with
  /- ## Expression or Equations -/
  | defnInfo defn => do
    if Expr.isComplexDef defn.value then
      if let some eqns ← getEqnsFor? expr.constName! then
        let mut output_array := #[]
        for eqnName in eqns do
          let next ← expr_rec (← getConstInfo eqnName).type .MultiLine styles fvars
          output_array := output_array.push next
        let output := "\\\\".intercalate output_array.toList
        let output' := s!"$$\\begin{"{"}cases{"}"}{output}\\end{"{"}cases{"}"}$$"
        return (output', NodeType.Text)
      else
        return none
    else
      return (← expr_rec defn.value parent styles fvars, parent)
  /- ## Theorem (or Lemma) -/
  | thmInfo thm => do
    return (← expr_rec thm.type parent styles fvars, parent)
  /- ## Axiom -/
  | axiomInfo _axiom => do
    return (← expr_rec _axiom.type parent styles fvars, parent)
  /- ## Inductive -/
  | inductInfo _ /- induct -/ =>
    return none
    /-
    let texType ← Expr2TeX induct.type
    queueLatexInfo box.getId s!"{nameStr}_type" texType
    let mut idx := 1
    for ctorName in induct.ctors do
        let ctorDecl ← getConstInfo ctorName
        let ctorTex ← Expr2TeX ctorDecl.type
        let outName := s!"{nameStr}_ctor{idx}"
        queueLatexInfo box.getId outName ctorTex
        idx := idx + 1
    -/
  /- ## Constructor -/
  | ctorInfo _ =>
    return none
  /- ## Recursor/Eliminator -/
  | recInfo _ => do
    return none
  /- ## Opaque -/
  | opaqueInfo _ => do
    return none
  /- ## Quotient Info -/
  | quotInfo _ => do
    return none

end Lean2TeX
