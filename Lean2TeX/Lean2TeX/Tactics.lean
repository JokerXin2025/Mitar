import Lean2TeX.Core

open Lean2TeX
open Lean Elab Tactic

private def addObj  (box : TSyntax `ident)
                    (name : Option (TSyntax `str))
                    (args : Array (TSyntax `ident))
                    (arg_keys : Array (Option (TSyntax `str)))
                    (ptrs : Array (TSyntax `ident))
                    (ptr_keys : Array (Option (TSyntax `str)))
                    (arrs : Array (TSyntax `ident))
                    (arr_keys : Array (Option (TSyntax `str)))
                    (withGoal : Bool)
                    : TacticM Unit := do
  /- `withMainContext` is essential: tactic elaboration runs in a scope where
     binders introduced by earlier tactics (e.g. `intro hP`) are NOT in the
     bare `getLCtx`; only the main goal's context has them.  However,
     `withMainContext` fails when there are no goals left (e.g. after a
     `cases` closes all branches), so we guard on `getGoals`. -/
  let goals ← getGoals
  if goals.isEmpty then
    /- No goal: record name + ptr/arr links (goal/args need a goal context). -/
    let mut PropertiesList := []
    if let some name! := name then
      PropertiesList := PropertiesList.concat ("name", Json.str name!.getString)
    /- Add JSON objects by pointers -/
    let mut ptr_index := 1
    let boxes ← JSON_boxes.get
    for (ptr, ptr_key) in ptrs.zip ptr_keys do
      let ptrName := ptr.getId
      match boxes.findIdx? (fun (b, _) => b == ptrName) with
      | some idx =>
        if boxes[idx]!.2.isEmpty then
          logWarning m! "[Lean2TeX] Box '{ptrName}' has been dumped."
        else
          if let some ptr_key! := ptr_key then
            PropertiesList := PropertiesList.concat (ptr_key!.getString, boxes[idx]!.2[0]!)
          else
            PropertiesList := PropertiesList.concat (s!"ptr_{ptr_index}", boxes[idx]!.2[0]!)
          JSON_boxes.set (boxes.set! idx (ptrName, #[]))
      | none =>
        logWarning m! "[Lean2TeX] Box '{ptrName}' has not been initialized."
      ptr_index := ptr_index + 1
    /- Add JSON arrays -/
    let mut arr_index := 1
    let boxes ← JSON_boxes.get
    for (arr, arr_key) in arrs.zip arr_keys do
      let arrName := arr.getId
      match boxes.findIdx? (fun (b, _) => b == arrName) with
      | some idx =>
        if let some arr_key! := arr_key then
          PropertiesList := PropertiesList.concat (arr_key!.getString, Json.arr boxes[idx]!.2)
        else
          PropertiesList := PropertiesList.concat (s!"arr_{arr_index}", Json.arr boxes[idx]!.2)
        JSON_boxes.set (boxes.set! idx (arrName, #[]))
      | none =>
        logWarning m! "[Lean2TeX] Box '{arrName}' has not been initialized."
      arr_index := arr_index + 1
    addtoBox box.getId (Json.mkObj PropertiesList)
    evalTactic (← `(tactic| skip))
  else
    withMainContext do
      /- Initialize `PropertiesList` -/
      let mut PropertiesList := []
      if let some name! := name then
        PropertiesList := PropertiesList.concat (
          "name", Json.str name!.getString
        )
      if withGoal then
        PropertiesList := PropertiesList.concat (
          "goal", Json.str (← Expr2TeX (← GetGoal) .only .Text [.Root] [])
        )
      /- Add arguments to `PropertiesList` -/
      let mut arg_index := 1
      for (arg, arg_key) in args.zip arg_keys do
        let expr ← instantiateMVars (← elabTerm arg none)
        if let some arg_key! := arg_key then
          PropertiesList := PropertiesList.concat (
            arg_key!.getString, Json.str (← Expr2TeX expr .only .Text [.Root] [])
          )
        else
          PropertiesList := PropertiesList.concat (
            s!"arg_{arg_index}", Json.str (← Expr2TeX expr .only .Text [.Root] [])
          )
        arg_index := arg_index + 1
      /- Add JSON objects to `PropertiesList` by pointers -/
      let mut ptr_index := 1
      let boxes ← JSON_boxes.get
      for (ptr, ptr_key) in ptrs.zip ptr_keys do
        let ptrName := ptr.getId
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
      let boxes ← JSON_boxes.get
      for (arr, arr_key) in arrs.zip arr_keys do
        let arrName := arr.getId
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

private def addVals (box : TSyntax `ident)
                    (ptrs : Array (TSyntax `ident))
                    (arrs : Array (TSyntax `ident))
                    : TacticM Unit := do
  /- Initialize `ItemsList` -/
  let mut ItemsList := []
  /- Add JSON objects to `ItemsList` by pointers -/
  let boxes ← JSON_boxes.get
  for ptr in ptrs do
    let ptrName := ptr.getId
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
  let boxes ← JSON_boxes.get
  for arr in arrs do
    let arrName := arr.getId
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

/-- Add information to a JSON box -/
syntax "Lean2TeX" ident "<-"
    (str)? ("_goal_")? (colGt ident ("(" str ")")?)*
    (colGt "*" ident ("(" str ")")?)* (colGt "&" ident ("(" str ")")?)* : tactic
/-- Merge JSON values into a new JSON box -/
syntax "Lean2TeX" "vals" ident "<-"
    (colGt "*" ident)* (colGt "&" ident)* : tactic

elab_rules : tactic
| `(tactic| Lean2TeX $box:ident <-
    $[$name:str]? $[$args:ident$[($arg_keys:str)]?]*
    $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  addObj box name args arg_keys ptrs ptr_keys arrs arr_keys false
| `(tactic| Lean2TeX $box:ident <-
    $[$name:str]? _goal_ $[$args:ident$[($arg_keys:str)]?]*
    $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  addObj box name args arg_keys ptrs ptr_keys arrs arr_keys true
| `(tactic| Lean2TeX vals $box:ident <-
    $[* $ptrs:ident]* $[& $arrs:ident]*) =>
  addVals box ptrs arrs
