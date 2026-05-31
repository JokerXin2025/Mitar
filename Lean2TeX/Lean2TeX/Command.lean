import Lean2TeX.Basic
import Lean2TeX.ExpressionRecursion

open Lean2TeX
open Lean Elab Term Command

syntax "#Lean2TeX_const " ident : command
syntax "Lean2TeX " ident " -> " ident : command
syntax "Lean2TeX " ident " => " str : command

elab_rules : command
| `(#Lean2TeX_const $const:ident) => do
  liftTermElabM do
  /- # View the definition of a constant -/
    let expr ← instantiateMVars (← elabTerm const none)
    let output ← Expr2TeX expr .Text .Def
    logInfo m! "[Lean2TeX] {const} :\n{output}"
| `(Lean2TeX $box:ident => $file:str) => do
  /- # Export the JSON array to a JSON file -/
  liftCoreM do
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
