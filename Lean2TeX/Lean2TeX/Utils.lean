import Lean2TeX.Basic

open Lean Elab Meta Expr Tactic

namespace Lean2TeX

namespace Lean

namespace Meta

partial def existsTelescope (expr : Expr) (expr_pass : ExprPassFunc) : MetaM String := do
  if expr.isAppOfArity' ``Exists 2 then
    return ← lambdaBoundedTelescope expr.getAppArgs'[1]! 1 fun newFvar body => do
      existsTelescope body fun restFvars finalBody =>
        expr_pass (newFvar ++ restFvars) finalBody
  else
    expr_pass #[] expr

end Meta

namespace Expr

def isComplexDef (expr : Expr) : Bool :=
  Option.isSome <| expr.find? fun
    | .const n _ =>
      let s := n.toString
      s.contains "brecOn" ||
      s.contains "casesOn" ||
      s.contains "recOn"
    | _ => false

end Expr

namespace Tactic

def RefreshGoal : TacticM Unit := do
  /- Refresh the goal to eliminate the warning -/
  let goal ← getMainGoal
  let goal_expr ← goal.getType
  let goal_tag ← goal.getTag
  let new_goal ← mkFreshExprSyntheticOpaqueMVar goal_expr goal_tag
  goal.assign new_goal
  replaceMainGoal [new_goal.mvarId!]

end Tactic

end Lean

namespace NodeInfo

def WrappedIn (nodeInfo : NodeInfo) (parent : OperNode) : MetaM String := do
  let mut (expr, node) := nodeInfo
  /- bracket the expression with `(` and `)` -/
  if node == .Add && parent == .Mul then
    expr := s!"\\left({expr}\\right)"
  /- bracket the expression with `$` -/
  if node != .Text && parent == .Text then
    expr := s!" ${expr}$ "
  /- bracket the expression with `\text{` and `}` -/
  if node == .Text && parent != .Text then
    expr := s!"\\text{"{"}{expr}{"}"}"
  return expr

end NodeInfo

end Lean2TeX
