import Lean2TeX.Basic

open Lean Elab Meta

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

def RefreshGoal : Tactic.TacticM Unit := do
  /- Refresh the goal to eliminate the warning -/
  let goal ← Tactic.getMainGoal
  let goal_expr ← goal.getType
  let goal_tag ← goal.getTag
  let new_goal ← mkFreshExprSyntheticOpaqueMVar goal_expr goal_tag
  goal.assign new_goal
  Tactic.replaceMainGoal [new_goal.mvarId!]

end Tactic
