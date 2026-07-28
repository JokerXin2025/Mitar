import Lean2TeX.Constant
import Lean2TeX.Rules

open Lean2TeX NodeInfo
namespace Lean2TeX


/-- 这些作用器无需打印 直接将特定索引的内容递交递归器 后续将封装进外部配置文件以便维护 -/
def UnwrapRegistry : List (Name × Nat) := [
  (``OfNat.ofNat, 1),
  (``Nat.cast, 2),
  (``Int.cast, 2)
]

partial def Expr2TeX (expr : Expr) (parent : NodeType) (styles : List DisplayType) (fvars : List (FVarId × String)) : MetaM String := do
  /- Match with preseted metarules -/
  for (name, argIdx) in UnwrapRegistry do
    if expr.getAppFn.isConstOf name then
      let args := expr.getAppArgs'
      if _ : argIdx < args.size then  -- Safety Check
        return (← Expr2TeX args[argIdx] parent styles fvars, parent).WrappedIn 1 parent
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
  | .forallE _ _ _ _ =>
    let res ← lambdaTelescope expr fun _ body =>
      Expr2TeX body parent role styles fvars
    return ← (res, parent, role).WrappedIn parent
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

