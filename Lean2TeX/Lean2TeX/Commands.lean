import Lean2TeX.Core

open Lean2TeX
open Lean Elab Command Term

/-- View constant's definition -/
elab "#Lean2TeX_const" const:ident : command => liftTermElabM do
  let expr ← instantiateMVars (← elabTerm const none)
  let output ← Expr2TeX expr .Text [.Def] []
  logInfo m! "[Lean2TeX] {const} :\n{output}"

/-- Export JSON box into a JSON file (as JSON array) -/
elab "Lean2TeX" box:ident "=>" file:str : command => do
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
