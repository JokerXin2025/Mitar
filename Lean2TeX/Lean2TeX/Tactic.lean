import Lean2TeX.Defs
import Lean2TeX.ExpressionRecursion

open Lean2TeX
open Lean Elab Tactic

namespace Lean2TeX.Tactic

def addObj (box : TSyntax `ident)
           (name : Option (TSyntax `str))
           (args : Array (TSyntax `ident))
           (arg_keys : Array (Option (TSyntax `str)))
           (ptrs : Array (TSyntax `ident))
           (ptr_keys : Array (Option (TSyntax `str)))
           (arrs : Array (TSyntax `ident))
           (arr_keys : Array (Option (TSyntax `str)))
           (withGoal : Bool := false)
           : TacticM Unit := withMainContext do
  /- Initialize `PropertiesList` -/
  let mut PropertiesList := []
  if let some name! := name then
    PropertiesList := PropertiesList.concat (
      "name", Json.str name!.getString
    )
  if withGoal then
    PropertiesList := PropertiesList.concat (
      "goal", Json.str (← Expr2TeX (← GetGoal) .Text [.Root] [])
    )
  /- Add arguments to `PropertiesList` -/
  let mut arg_index := 1
  for (arg, arg_key) in args.zip arg_keys do
    let expr ← instantiateMVars (← elabTerm arg none)
    if let some arg_key! := arg_key then
      PropertiesList := PropertiesList.concat (
        arg_key!.getString, Json.str (← Expr2TeX expr .Text [.Root] [])
      )
    else
      PropertiesList := PropertiesList.concat (
        s!"arg_{arg_index}", Json.str (← Expr2TeX expr .Text [.Root] [])
      )
    arg_index := arg_index + 1
  /- Add JSON objects to `PropertiesList` by pointers -/
  let mut ptr_index := 1
  let mut ptrName := Name.anonymous
  let boxes ← JSON_boxes.get
  for (ptr, ptr_key) in ptrs.zip ptr_keys do
    ptrName := ptr.getId
    match boxes.findIdx? (fun (b, _) => b == ptrName) with
    | some idx =>
      if boxes[idx]!.2.isEmpty then
        logWarning m! "[Lean2TeX] Box '{ptrName}' has been dumped."
      else
        if let some ptr_key! := ptr_key then
          PropertiesList := PropertiesList.concat (
            ptr_key!.getString, boxes[idx]!.2[0]!
          )
        else
          PropertiesList := PropertiesList.concat (
            s!"ptr_{ptr_index}", boxes[idx]!.2[0]!
          )
        JSON_boxes.set (boxes.set! idx (ptrName, #[]))
    | none =>
      logWarning m! "[Lean2TeX] Box '{ptrName}' has not been initialized."
    ptr_index := ptr_index + 1
  /- Add JSON arrays to `PropertiesList` -/
  let mut arr_index := 1
  let mut arrName := Name.anonymous
  let boxes ← JSON_boxes.get
  for (arr, arr_key) in arrs.zip arr_keys do
    arrName := arr.getId
    match boxes.findIdx? (fun (b, _) => b == arrName) with
    | some idx =>
      if let some arr_key! := arr_key then
        PropertiesList := PropertiesList.concat (
          arr_key!.getString, Json.arr boxes[idx]!.2
        )
      else
        PropertiesList := PropertiesList.concat (
          s!"arr_{arr_index}", Json.arr boxes[idx]!.2
        )
      JSON_boxes.set (boxes.set! idx (arrName, #[]))
    | none =>
      logWarning m! "[Lean2TeX] Box '{arrName}' has not been initialized."
    arr_index := arr_index + 1
  /- Make JSON object -/
  addtoBox box.getId (Json.mkObj PropertiesList)
  /- Refresh the goal to eliminate the warning -/
  evalTactic (← `(tactic| skip))

def addVals (box : TSyntax `ident)
            (ptrs : Array (TSyntax `ident))
            (arrs : Array (TSyntax `ident))
            : TacticM Unit := withMainContext do
  /- Initialize `ItemsList` -/
  let mut ItemsList := []
  /- Add JSON objects to `ItemsList` by pointers -/
  let mut ptrName := Name.anonymous
  let boxes ← JSON_boxes.get
  for ptr in ptrs do
    ptrName := ptr.getId
    match boxes.findIdx? (fun (b, _) => b == ptrName) with
    | some idx =>
      if boxes[idx]!.2.isEmpty then
        logWarning m! "[Lean2TeX] Box '{ptrName}' has been dumped."
      else
        ItemsList := ItemsList.concat (
          boxes[idx]!.2[0]!
        )
        JSON_boxes.set (boxes.set! idx (ptrName, #[]))
    | none =>
      logWarning m! "[Lean2TeX] Box '{ptrName}' has not been initialized."
  /- Add JSON arrays to `ItemsList` -/
  let mut arrName := Name.anonymous
  let boxes ← JSON_boxes.get
  for arr in arrs do
    arrName := arr.getId
    match boxes.findIdx? (fun (b, _) => b == arrName) with
    | some idx =>
      ItemsList := ItemsList.concat (
        Json.arr boxes[idx]!.2
      )
      JSON_boxes.set (boxes.set! idx (arrName, #[]))
    | none =>
      logWarning m! "[Lean2TeX] Box '{arrName}' has not been initialized."
  /- Add JSON values to JSON box -/
  for val in ItemsList do
    addtoBox box.getId val
  /- Refresh the goal to eliminate the warning -/
  evalTactic (← `(tactic| skip))

end Lean2TeX.Tactic

syntax "Lean2TeX" ident "<-"
    (str)? ("_goal_")? (colGt ident ("(" str ")")?)*
    (colGt "*" ident ("(" str ")")?)* (colGt "&" ident ("(" str ")")?)* : tactic
syntax "Lean2TeX" "vals" ident "<-"
    (colGt "*" ident)* (colGt "&" ident)* : tactic

elab_rules : tactic
| `(tactic| Lean2TeX $box:ident <-
    $[$name:str]? $[$args:ident$[($arg_keys:str)]?]*
    $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  /- ## Add information to a JSON array -/
  Lean2TeX.Tactic.addObj box name args arg_keys ptrs ptr_keys arrs arr_keys
| `(tactic| Lean2TeX $box:ident <-
    $[$name:str]? _goal_ $[$args:ident$[($arg_keys:str)]?]*
    $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  /- ## Add information to a JSON array (with current goal) -/
  Lean2TeX.Tactic.addObj box name args arg_keys ptrs ptr_keys arrs arr_keys true
| `(tactic| Lean2TeX vals $box:ident <-
    $[* $ptrs:ident]* $[& $arrs:ident]*) =>
  /- ## Merge JSON values into a new JSON array -/
  Lean2TeX.Tactic.addVals box ptrs arrs
