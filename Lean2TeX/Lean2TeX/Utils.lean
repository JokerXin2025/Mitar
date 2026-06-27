import Lean2TeX.Defs

open Lean Elab Meta Expr Tactic

namespace Lean2TeX

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

def GetGoal : TacticM Expr := do
  /- # Get the expression of current Goal -/
  let goal ← getMainGoal
  let goal_expr ← goal.getType
  return ← instantiateMVars goal_expr

end Tactic

def addtoBox (box : Name) (json_obj : Json) : MetaM Unit := do
  /- # Add JSON objects `json_obj` to the JSON array -/
  JSON_boxes.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == box) with
    | some idx =>
      let (b, items) := arr[idx]!
      arr.set! idx (b, items.push json_obj)
    | none =>
      /- create the JSON array for the first time -/
      arr.push (box, #[json_obj])

def NodeInfo.WrappedIn (nodeInfo : NodeInfo) (parent : NodeType) : MetaM String := do
  let mut (expr, node) := nodeInfo
  /- Operation Priority -/
  if node == .Add && parent == .Mul then
    expr := s!"\\left({expr}\\right)"
  /- Base of Power Expression -/
  if (node == .Add || node == .Mul || node == .Supscript) && parent == .BySupscript then
    expr := s!"\\left({expr}\\right)"
  /- Inline Equation -/
  if node != .Text && parent == .Text then
    expr := s!" ${expr}$ "
  /- Embedded Text -/
  if node == .Text && parent != .Text then
    expr := s!"\\text{"{"}{expr}{"}"}"
  return expr

end Lean2TeX
