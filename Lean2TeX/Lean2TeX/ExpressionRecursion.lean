import Lean2TeX.Basic
import Lean2TeX.Utils
import Lean2TeX.Constant
import Lean2TeX.Variable
import Lean2TeX.Rules

open Lean2TeX NodeInfo

namespace Lean2TeX

partial def Expr2TeX (expr : Expr) (parent : OperNode) (style : TeXStyle) : MetaM String := do
  /- Match with preseted rules of same `TeXstyle` -/
  for (metarule) in PresetMetaRules do
    if let some res ← metarule expr.consumeMData parent style Expr2TeX then
      return ← res.WrappedIn parent
  for (rule, rule_style) in PresetRules do
    if style == rule_style then
      if let some res ← rule expr.consumeMData Expr2TeX then
        return ← res.WrappedIn parent
  /- Match with preseted rules of `.Basic` by default -/
  for (metarule) in PresetMetaRules do
    if let some res ← metarule expr.consumeMData parent style Expr2TeX then
      return ← res.WrappedIn parent
  for (rule, rule_style) in PresetRules do
    if rule_style == .Basic then
      if let some res ← rule expr.consumeMData Expr2TeX then
        return ← res.WrappedIn parent
  /- Error Handling & Core Procession -/
  match expr with
  | .sort _ => return "[sort]"
  | .bvar _ => return "[bvar]"
  | .mvar _ => return "[mvar]"
  | .proj _ _ _ => return "[proj]"
  | .lam _ _ _ _ => return "[lam]"
  -- This case will never be executed, according to function `MetaRule_Lambda` .
  | .forallE _ _ _ _ => return "[forallE]"
  -- This case will never be executed, according to function `Rule_Implies` and `Rule_Forall` .
  | .letE _ _ _ _ _ => return "[letE]"
  | .lit (.natVal n) => return ← WrappedIn (s!"{n}", .Unit) parent
  | .lit (.strVal s) => return ← WrappedIn (s, .Text) parent
  | .app fn arg => do
    let f ← Expr2TeX fn .BracApp style
    let x ← Expr2TeX arg .BracApp style
    return ← WrappedIn (s!"{f}[{x}]", .BracApp) parent
  | .const const _ =>
    if style == .Def then
      if let some res ← expr.getConstDef parent style (Expr2TeX · · ·) then
        return ← res.WrappedIn parent
      else
        return ""
    else
      return ← WrappedIn (const.toString, .Unit) parent  -- !
  | .fvar var => do
    let decl ← var.getDecl
    match decl.value? with
    | some val => return ← Expr2TeX val parent style
    | none =>
      if ← isProp decl.type then
        return ← Expr2TeX decl.type parent style
      else
        return ← WrappedIn (decl.userName.toString, .Unit) parent  -- !
  | .mdata _ expr' => Expr2TeX expr' parent style

end Lean2TeX
