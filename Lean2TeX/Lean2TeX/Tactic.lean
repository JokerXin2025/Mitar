import Lean2TeX.Basic
import Lean2TeX.ExpressionRecursion

open Lean2TeX
open Lean Elab Tactic

syntax "Lean2TeX_step " ident " <- " (colGt ident)+ (" | " colGt term)? : tactic
syntax "Lean2TeX_state " ident " <- " " goal " (colGt ident)* : tactic

elab_rules : tactic

| `(tactic| Lean2TeX_step $box:ident <- $tactic:ident $args:ident* $[| $arg_term:term]?) =>
  withMainContext do

    let mut NewStepList := [
      ("step", Json.str tactic.getId.toString)
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

    let mut NewRecordList := [
      ("goal", Json.str (← Expr2TeX (← GetGoal) .Text .Root))
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
