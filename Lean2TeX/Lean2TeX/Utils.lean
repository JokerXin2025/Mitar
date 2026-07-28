import Lean2TeX.Prelude

namespace Lean2TeX


open Lean Meta in
/-- `∃` counterpart of `lambdaTelescope` and `forallTelescope` -/
partial def existsTelescope (expr : Expr)
                            (expr_pass : Array Expr → Expr → MetaM String)
                            : MetaM String := do
  if expr.isAppOfArity' ``Exists 2 then
    return ← lambdaBoundedTelescope expr.getAppArgs'[1]! 1 fun newFvar body => do
      existsTelescope body fun restFvars finalBody =>
        expr_pass (newFvar ++ restFvars) finalBody
  else
    expr_pass #[] expr

open Lean Elab.Tactic in
/-- Get the expression of current goal -/
def GetGoal : TacticM Expr := do
  let goal ← getMainGoal
  let goal_expr ← goal.getType
  return ← instantiateMVars goal_expr

/-- Add JSON objects `json_obj` to the JSON array -/
def addtoBox  (box : Name)
              (json_obj : Json)
              : MetaM Unit := do
  JSON_boxes.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == box) with
    | some idx =>
      let (b, items) := arr[idx]!
      arr.set! idx (b, items.push json_obj)
    | none =>
      /- create the JSON array for the first time -/
      arr.push (box, #[json_obj])

/-- Automatic TeX Wrapper based on `NodeType` and `NodeRole` -/
def NodeInfo.WrappedIn  (nodeInfo : NodeInfo)
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
end Lean2TeX
