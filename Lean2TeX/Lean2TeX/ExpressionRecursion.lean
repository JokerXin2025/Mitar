import Lean2TeX.Basic
import Lean2TeX.Utils
import Lean2TeX.Constant
import Lean2TeX.Variable
import Lean2TeX.Rules

open Lean Elab Meta Command Tactic

partial def Expr2TeX (e : Expr) (style : TeXStyle) : MetaM String := do
  /- Preseted Rules -/
  for (rule, rule_style) in Rules do
    if style == rule_style || style == .Root then
      if let some res ← rule e.consumeMData Expr2TeX then return res
  /- Error Handling & Core Procession -/
  match e with
  | .sort _ => return "[sort]"
  | .bvar _ => return "[bvar]"
  | .mvar _ => return "[mvar]"
  | .lam _ _ _ _ => return "[lam]"
  | .letE _ _ _ _ _ => return "[letE]"
  | .lit (.natVal n) => return s!"{n}"
  | .lit (.strVal s) => return s!"\\text{"{"}{s}{"}"}"
  | .app fn arg => do
    let f ← Expr2TeX fn Basic
    let x ← Expr2TeX arg Basic
    return s!"\\Action{"{"}{f}{"}"}{"{"}{x}{"}"}"
  | .const const _ =>
    if style == Def then
      return ← getConstDef const (Expr2TeX · ·)
    else
      return const.toString
  | .proj _ _ _ => do
    return ""
  | .fvar var => do
    let x ← var.getUserName
    return s!"VarName{"{"}{x}{"}"}"
  | .forallE _ type _ _ => do
      if e.isArrow then
        let res ← forallBoundedTelescope e (some 1) fun _ body => do
          let XXX ← Expr2TeX type Basic
          let YYY ← Expr2TeX body Basic
          return s!"\\Implies{"{"}{XXX}{"}"}{"{"}{YYY}{"}"}"
        return res
      else
        let res ← forallBoundedTelescope e (some 1) fun fvars body => do
          let fvar := fvars[0]!
          let x ← fvar.fvarId!.getUserName
          let A ← Expr2TeX type Basic
          let XXX ← Expr2TeX body Basic
          return s!"\\Forall{"{"}\\VarName{"{"}{x}{"}"}{"}"}{"{"}{A}{"}"}{"{"}{XXX}{"}"}"
        return res
  | .mdata _ expr => Expr2TeX expr Basic
