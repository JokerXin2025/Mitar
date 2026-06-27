import Lean2TeX.Defs
import Lean2TeX.ExpressionRecursion

open Lean2TeX
open Lean Elab Command
open Lean.Elab.Term (elabTerm)

namespace Lean2TeX.Command

def addObj (box : TSyntax `ident)
           (name : Option (TSyntax `str))
           (ptrs : Array (TSyntax `ident))
           (ptr_keys : Array (Option (TSyntax `str)))
           (arrs : Array (TSyntax `ident))
           (arr_keys : Array (Option (TSyntax `str)))
           : CommandElabM Unit := do
  /- Initialize `PropertiesList` -/
  let mut PropertiesList := []
  if let some name! := name then
    PropertiesList := PropertiesList.concat (
      "name", Json.str name!.getString
    )
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
  /- Make JSON object and add it to JSON box -/
  liftTermElabM do addtoBox box.getId (Json.mkObj PropertiesList)

def addVals (box : TSyntax `ident)
            (ptrs : Array (TSyntax `ident))
            (arrs : Array (TSyntax `ident))
            : CommandElabM Unit := do
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
    liftTermElabM do addtoBox box.getId val

end Lean2TeX.Command

syntax "#Lean2TeX_const" ident : command
syntax "Lean2TeX" ident "<-"
    (str)? (colGt "*" ident ("(" str ")")?)* (colGt "&" ident ("(" str ")")?)* : command
syntax "Lean2TeX" "vals" ident "<-"
    (colGt "*" ident)* (colGt "&" ident)* : command
syntax "Lean2TeX" ident "=>" str : command

elab_rules : command
| `(command| #Lean2TeX_const $const:ident) => liftTermElabM do
  /- ## View constant's definition -/
  let expr ← instantiateMVars (← elabTerm const none)
  let output ← Expr2TeX expr .Text [.Def] []
  logInfo m! "[Lean2TeX] {const} :\n{output}"
| `(command| Lean2TeX $box:ident <-
    $[$name:str]? $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  /- ## Merge JSON values into a new JSON object -/
  Lean2TeX.Command.addObj box name ptrs ptr_keys arrs arr_keys
| `(command| Lean2TeX vals $box:ident <-
    $[* $ptrs:ident]* $[& $arrs:ident]*) =>
  /- ## Merge JSON values into a new JSON array -/
  Lean2TeX.Command.addVals box ptrs arrs
| `(command| Lean2TeX $box:ident => $file:str) => do
  /- ## Export JSON box into a JSON file (as JSON array) -/
  let boxName := box.getId
  let arr ← JSON_boxes.get
  match arr.findIdx? (fun (b, _) => b == boxName) with
  | some idx =>
    let (_, currentData) := arr[idx]!
    if currentData.isEmpty then
      logWarning m! "[Lean2TeX] Box '{boxName}' has been dumped."
    else
      IO.FS.writeFile file.getString (Json.arr currentData).pretty
      JSON_boxes.set (arr.set! idx (boxName, #[]))
  | none =>
    logWarning m! "[Lean2TeX] Box '{boxName}' has not been initialized."
