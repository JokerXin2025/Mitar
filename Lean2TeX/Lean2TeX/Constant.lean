import Lean2TeX.Basic
import Lean2TeX.Utils

open Lean Meta ConstantInfo

def getConstDef (name : Name) (expr_rec : ExprRecFunc) : MetaM String := do
  match ← getConstInfo name with
  /- Normal Definition: Expression or Equations -/
  | defnInfo defn => do
    if Expr.isComplexDef defn.value then
      if let some eqns ← getEqnsFor? name then
        let mut texcode := ""
        for eqnName in eqns do
          texcode := texcode ++ (← expr_rec (← getConstInfo eqnName).type Basic)
        return texcode
      else
        return ""  -- silence
    else
      return ← expr_rec defn.value Basic
  /- Theorem (or Lemma) -/
  | thmInfo thm => do
    return ← expr_rec thm.type Basic
  /- Axiom -/
  | axiomInfo _axiom => do
    return ← expr_rec _axiom.type Basic
  /- Inductive (i.e. Nat) -/
  | inductInfo _ /- induct -/ =>
    return ""  -- silence
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
  /- Constructor (i.e. Nat.zero, Nat.succ) -/
  | ctorInfo _ =>
    return ""  -- silence
  /- Recursor/Eliminator (i.e. Nat.rec) -/
  | recInfo _ => do
    return ""  -- silence
  /- Opaque -/
  | opaqueInfo _ => do
    return ""  -- silence
  /- Quotient Info -/
  | quotInfo _ => do
    return ""  -- silence
