import Lean2TeX.Basic
import Lean2TeX.ExpressionRecursion

open Lean2TeX
open Lean Elab Meta Tactic

def GetGoal : TacticM String := do
  /- # Add JSON objects `json_obj` to the JSON array -/
  let goal ← getMainGoal
  let goal_expr ← goal.getType
  let goal_expr' ← instantiateMVars goal_expr
  return ← Expr2TeX goal_expr' .Text .Root

def AddtoJsonArray (box : Name) (json_obj : Json) : MetaM Unit := do
  /- # Add JSON objects `json_obj` to the JSON array -/
  JSON_boxes.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == box) with
    | some idx =>
      let (b, items) := arr[idx]!
      arr.set! idx (b, items.push json_obj)
    | none =>  -- create the JSON array for the first time
      arr.push (box, #[json_obj])

syntax "Lean2TeX_step " ident " <- " (colGt ident)+ (" | " colGt term)? : tactic
syntax "Lean2TeX_state " ident " <- " " goal " (colGt ident)* : tactic

elab_rules : tactic
| `(tactic| Lean2TeX_step $box:ident <- $tactic:ident $args:ident* $[| $arg_term:term]?) =>
  withMainContext do

  /- __· Use this tactic before the step ·__ -/

    let mut NewStepList := [
      ("tacticId", Json.str tactic.getId.toString)
    ]

    /- Add argument variables to `NewStepList` -/
    let mut var_index := 1
    for var in args do
      let expr ← instantiateMVars (← elabTerm var none)
      NewStepList := NewStepList.concat (
        s!"arg_{var_index}", Json.str (← Expr2TeX expr .Text .Root)
      )
      var_index := var_index + 1

    /- Add argument expression to `NewStepList` -/
    if let some expr_term := arg_term then
      let expr ← instantiateMVars (← elabTerm expr_term none)
      let expr_type ← instantiateMVars (← inferType expr)
      let expr' := if ← isProp expr_type then expr_type else expr
      NewStepList := NewStepList.concat (
        "expr", Json.str (← Expr2TeX expr' .Text .Root)
      )

    AddtoJsonArray box.getId (Json.mkObj NewStepList)
    RefreshGoal

|`(tactic| Lean2TeX_state $box:ident <- goal $ids:ident*) =>
  withMainContext do

  /- _· Use this tactic after the non-final step ·_ -/

    let mut NewRecordList := [
      ("goal", Json.str (← GetGoal))
    ]

    /- Add argument variables to `NewRecordList` -/
    let mut var_index := 1
    for var in ids do
      let expr ← instantiateMVars (← elabTerm var none)
      NewRecordList := NewRecordList.concat (
        s!"id_{var_index}", Json.str (← Expr2TeX expr .Text .Root)
      )
      var_index := var_index + 1

    AddtoJsonArray box.getId (Json.mkObj NewRecordList)
    RefreshGoal
