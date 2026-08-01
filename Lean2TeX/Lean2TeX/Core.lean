import Lean2TeX.Constant
import Lean2TeX.Rules

open Lean2TeX
open Lean.Meta (lambdaTelescope)
namespace Lean2TeX


/-- Automatic TeX Wrapper based on `NodeType` and `NodeRole` -/
def AutoWrap  (nodeInfo : NodeInfo)
              (role : NodeRole)
              (parent : NodeType)
              : MetaM String := do
  let mut (expr, type) := nodeInfo
  /- Operation Priority -/
  if type == .Add && parent == .Mul then
    expr := s!"\\left({expr}\\right)"
  /- Base of Power Expression -/
  if role == .base && parent == .Supscript then
    if type == .Add || type == .Mul || type == .Supscript then
      expr := s!"\\left({expr}\\right)"
  /- Inline Equation -/
  if type != .Text && parent == .Text then
    expr := s!" ${expr}$ "
  /- Embedded Text -/
  if type == .Text && parent != .Text then
    expr := s!"\\text{"{"}{expr}{"}"}"
  return expr

partial def Expr2TeX (expr : Expr) (role : NodeRole) (parent : NodeType) (styles : List DisplayType) (fvars : List (FVarId × String)) : MetaM String := do
  /- Match with Unwrap Ext -/
  if let .const declName _ := expr.getAppFn then
    let env ← getEnv
    if let some argIdx := (UnwrapExt.getState env).find? declName then
      let args := expr.getAppArgs_'
      if _ : argIdx < args.size then  -- Safety Check
        let res ← Expr2TeX args[argIdx] role parent styles fvars
        return ← AutoWrap (res, parent) role parent

  /- Match with preseted rules of same `DisplayType` -/
  for (rule, rule_style) in PresetRules do
    if styles.contains rule_style then
      if let some res ← rule expr.consumeMData Expr2TeX styles fvars then
        return ← AutoWrap res role parent
  /- Match with preseted rules of `.Basic` by default -/
  for (rule, rule_style) in PresetRules do
    if rule_style == .Basic then
      if let some res ← rule expr.consumeMData Expr2TeX styles fvars then
        return ← AutoWrap res role parent
  /- Error Handling & Core Procession -/
  match expr with
  | .sort _ => return "[sort]"
  | .bvar _ => return "[bvar]"
  | .mvar _ => return "[mvar]"
  | .proj _ _ _ => return "[proj]"
  | .lam _ _ _ _ => return "[lam]"
  | .forallE _ _ _ _ =>
    let res ← lambdaTelescope expr fun _ body =>
      Expr2TeX body role parent styles fvars
    return ← AutoWrap (res, parent) role parent
  | .letE _ _ _ _ _ => return "[letE]"
  | .lit (.natVal n) => return ← AutoWrap (s!"{n}", .Unit) role parent
  | .lit (.strVal s) => return ← AutoWrap (s, .Text) role parent
  | .app fn arg => do
    let f ← Expr2TeX fn role .BracApp styles fvars
    let x ← Expr2TeX arg role .BracApp styles fvars
    return ← AutoWrap (s!"{f}[{x}]", .BracApp) role parent
  | .const const _ =>
    if styles.contains .Def then
      if let some res ← expr.getConstDef Expr2TeX role parent styles fvars then
        return ← AutoWrap res role parent
      else
        return ""
    else
      return ← AutoWrap (const.toString, .Unit) role parent  -- !
  | .fvar fvar => do
    let decl ← fvar.getDecl
    match decl.value? with
    | some val => return ← Expr2TeX val role parent styles fvars
    | none =>
      if ← isProp decl.type then
        return ← Expr2TeX decl.type role parent styles fvars
      else
        if let some fvar_name! := fvars.lookup fvar then
          return ← AutoWrap (fvar_name!, .Unit) role parent
        else
          return ← AutoWrap (decl.userName.toString, .Unit) role parent
  | .mdata _ expr' => Expr2TeX expr' role parent styles fvars

end Lean2TeX
