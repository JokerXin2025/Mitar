import Lean2TeX.Defs
import Lean2TeX.Utils
import Lean2TeX.Constant
import Lean2TeX.Rules

open Lean2TeX NodeInfo

namespace Lean2TeX

partial def Expr2TeX (expr : Expr) (parent : NodeType) (styles : List DisplayType) (fvars : List (FVarId × String)) : MetaM String := do
  /- Match with preseted metarules of same `DisplayType` -/
  for metarule in PresetMetaRules do
    if let some res ← metarule expr.consumeMData Expr2TeX parent styles fvars then
      return ← res.WrappedIn parent
  /- Match with preseted rules of same `DisplayType` -/
  for (rule, rule_style) in PresetRules do
    if styles.contains rule_style then
      if let some res ← rule expr.consumeMData Expr2TeX styles fvars then
        return ← res.WrappedIn parent
  /- Match with preseted rules of `.Basic` by default -/
  for (rule, rule_style) in PresetRules do
    if rule_style == .Basic then
      if let some res ← rule expr.consumeMData Expr2TeX styles fvars then
        return ← res.WrappedIn parent
  /- Error Handling & Core Procession -/
  match expr with
  | .sort _ => return "[sort]"
  | .bvar _ => return "[bvar]"
  | .mvar _ => return "[mvar]"
  | .proj _ _ _ => return "[proj]"
  | .lam _ _ _ _ => return "[lam]"
  /- This case will never be executed due to `MetaRule_Lambda` -/
  | .forallE _ _ _ _ => return "[forallE]"
  /- This case will never be executed due to `Rule_Implies` and `Rule_Forall` -/
  | .letE _ _ _ _ _ => return "[letE]"
  | .lit (.natVal n) => return ← WrappedIn (s!"{n}", .Unit) parent
  | .lit (.strVal s) => return ← WrappedIn (s, .Text) parent
  | .app fn arg => do
    let f ← Expr2TeX fn .BracApp styles fvars
    let x ← Expr2TeX arg .BracApp styles fvars
    return ← WrappedIn (s!"{f}[{x}]", .BracApp) parent
  | .const const _ =>
    if styles.contains .Def then
      if let some res ← expr.getConstDef Expr2TeX parent styles fvars then
        return ← res.WrappedIn parent
      else
        return ""
    else
      return ← WrappedIn (const.toString, .Unit) parent  -- !
  | .fvar fvar => do
    let decl ← fvar.getDecl
    match decl.value? with
    | some val => return ← Expr2TeX val parent styles fvars
    | none =>
      if ← isProp decl.type then
        return ← Expr2TeX decl.type parent styles fvars
      else
        if let some fvar_name! := fvars.lookup fvar then
          return ← WrappedIn (fvar_name!, .Unit) parent
        else
          return ← WrappedIn (decl.userName.toString, .Unit) parent
  | .mdata _ expr' => Expr2TeX expr' parent styles fvars

end Lean2TeX
