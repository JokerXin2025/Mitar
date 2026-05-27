import Lean2TeX.Basic
import Lean2TeX.ExpressionRecursion

open Lean Elab Command

syntax "#Lean2TeX_const " ident : command
syntax "Lean2TeX " ident " -> " ident : command
syntax "Lean2TeX " ident " => " str : command

elab_rules : command
| `(#Lean2TeX_const $const:ident) => do
  liftTermElabM do
    let name ← resolveGlobalConstNoOverload const
    logInfo m! "[Lean2TeX] {const} :\n{← getConstDef name Expr2TeX}"
| `(Lean2TeX $box:ident => $file:str) => do
  /- Export the JSON array to JSON file -/
  liftCoreM do
    let boxName := box.getId
    let arr ← JSON_boxes.get
    match arr.findIdx? (fun (b, _) => b == boxName) with
    | some idx =>
      let (_, currentData) := arr[idx]!
      if currentData.isEmpty then
        logWarning m! "[Lean2TeX] 暂存器 '{boxName}' 已清空"
      else
        IO.FS.writeFile file.getString (Json.arr currentData).pretty
        JSON_boxes.set (arr.set! idx (boxName, #[]))
    | none =>
      logWarning m! "[Lean2TeX] 暂存器 '{boxName}' 未启用"
