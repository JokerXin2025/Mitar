import Lean
import Lean2TeX.Rules

open Lean Elab Meta Tactic

partial def exprToLatex (e : Expr) (rootName : Option String := none) : MetaM String := do
  /- Preseted Rules -/
  for rule in Rules do
    if let some res ← rule e.consumeMData (fun x => exprToLatex x rootName) then return res
  /- Error Handling & Core Procession -/
  match e with
  | .sort _ => return "[sort]"
  | .bvar _ => return "[bvar]"
  | .mvar _ => return "[mvar]"
  | .lam _ _ _ _ => return "[lam]"
  | .letE _ _ _ _ _ => return "[letE]"
  | .lit (.natVal n) => return s! "{n}"
  | .lit (.strVal s) => return s! "\\text{"{"}{s}{"}"}"
  | .app fn arg => do
    let f ← exprToLatex fn rootName
    let x ← exprToLatex arg rootName
    return s! "\\Action{"{"}{f}{"}"}{"{"}{x}{"}"}"
  | .const cname _ =>
    let baseName := cname.components.getLast!.toString
    if some cname.toString == rootName then
      return s! "{baseName}"
    else
      return s! "@{baseName}"
  | .proj _ i Struct => do
    let S ← exprToLatex Struct rootName
    return s! "{S}{"{"}{i}{"}"}"
  | .fvar var => do
    let x ← var.getUserName
    return s! "\\VarName{"{"}{x}{"}"}"
  | .forallE _ type _ _ => do
      if e.isArrow then
        let res ← Meta.forallBoundedTelescope e (some 1) fun _ body => do
          let XXX ← exprToLatex type rootName
          let YYY ← exprToLatex body rootName
          return s! "\\Implies{"{"}{XXX}{"}"}{"{"}{YYY}{"}"}"
        return res
      else
        let res ← Meta.forallBoundedTelescope e (some 1) fun fvars body => do
          let fvar := fvars[0]!
          let x ← fvar.fvarId!.getUserName
          let A ← exprToLatex type rootName
          let XXX ← exprToLatex body rootName
          return s! "\\Forall{"{"}\\VarName{"{"}{x}{"}"}{"}"}{"{"}{A}{"}"}{"{"}{XXX}{"}"}"
        return res
  | .mdata _ expr => exprToLatex expr rootName

initialize latexExportState : IO.Ref (Array (Name × Array Json)) ← IO.mkRef #[]

def queueLatexInfo (box : Name) (id code : String) : IO Unit := do
  let jsonObj := Json.mkObj [
    ("id", Json.str id),
    ("code", Json.str code)
  ]
  latexExportState.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == box) with
    | some idx =>
      let (b, items) := arr[idx]!
      arr.set! idx (b, items.push jsonObj)
    | none =>
      arr.push (box, #[jsonObj])

syntax "Lean2TeX_goal" str " -> " ident : tactic
syntax "Lean2TeX_type" str " : " ident " <- " term : tactic
syntax "Lean2TeX_def " ident " -> " ident : command
syntax "Lean2TeX_prop " ident " -> " ident : command
syntax "Lean2TeX_export " ident " -> " str : command

def isComplexDef (e : Expr) : Bool :=
  Option.isSome <| e.find? fun
    | .const n _ =>
      let s := n.toString
      s.contains "brecOn" ||
      s.contains "casesOn" ||
      s.contains "recOn"
    | _ => false

elab_rules : tactic
| `(tactic| Lean2TeX_type $id:str : $box:ident <- $e:term) => do
  withMainContext do
    let mvarId ← getMainGoal
    let expr ← elabTerm e none
    let expr ← instantiateMVars expr
    let type ← inferType expr
    let type ← instantiateMVars type
    let isProof ← Meta.isProp type
    let targetExpr := if isProof then type else expr
    let texcode ← exprToLatex targetExpr none
    let boxName := box.getId
    let idStr := id.getString
    queueLatexInfo boxName idStr texcode
    logInfo m! "[Lean2TeX] 成功记录 '{idStr}' 到 '{boxName}' :\n{texcode}"
    let tag ← mvarId.getTag
    let newMVar ← mkFreshExprSyntheticOpaqueMVar (← mvarId.getType) tag
    mvarId.assign newMVar
    replaceMainGoal [newMVar.mvarId!]
| `(tactic| Lean2TeX_goal $id:str -> $box:ident) => do
  withMainContext do
    let mvarId ← getMainGoal
    let goalType ← mvarId.getType
    let goalExpr ← instantiateMVars goalType
    let texcode ← exprToLatex goalExpr none
    let boxName := box.getId
    let idStr := id.getString
    queueLatexInfo boxName idStr texcode
    logInfo m! "[Lean2TeX] 成功记录当前目标 '{idStr}' 到 '{boxName}' :\n{texcode}"
    let tag ← mvarId.getTag
    let newMVar ← mkFreshExprSyntheticOpaqueMVar goalType tag
    mvarId.assign newMVar
    replaceMainGoal [newMVar.mvarId!]

elab_rules : command
| `(Lean2TeX_def $id:ident -> $box:ident) => do
  Command.liftTermElabM do
    let name ← resolveGlobalConstNoOverload id
    let nameStr := name.toString
    let boxName := box.getId
    let decl ← getConstInfo name
    let mut usedEqns := false
    if let some val := decl.value? then
      if isComplexDef val then
        if let some eqns ← Meta.getEqnsFor? name then
          usedEqns := true
          for (eqnName, idx) in eqns.zip (Array.range eqns.size) do
            let eqnDecl ← getConstInfo eqnName
            let texcode ← exprToLatex eqnDecl.type (some nameStr)
            let outName := s! "{nameStr}_eq{idx+1}"
            queueLatexInfo boxName outName texcode
            logInfo m! "[Lean2TeX] 成功记录方程 '{outName}' 到 '{boxName}' :\n{texcode}"
    if !usedEqns then
      if let some val := decl.value? then
        let texcode ← exprToLatex val (some nameStr)
        queueLatexInfo boxName nameStr texcode
        logInfo m! "[Lean2TeX] 成功记录 '{nameStr}' 到 '{boxName}' :\n{texcode}"
| `(Lean2TeX_prop $id:ident -> $box:ident) => do
  Command.liftTermElabM do
    let name ← resolveGlobalConstNoOverload id
    let nameStr := name.toString
    let boxName := box.getId
    let decl ← getConstInfo name
    let texcode ← exprToLatex decl.type none
    queueLatexInfo boxName nameStr texcode
    logInfo m! "[Lean2TeX] 成功记录命题 '{nameStr}' 到 '{boxName}' :\n{texcode}"
| `(Lean2TeX_export $box:ident -> $file:str) => do
  Command.liftCoreM do
    let boxName := box.getId
    let arr ← latexExportState.get
    match arr.findIdx? (fun (b, _) => b == boxName) with
    | some idx =>
      let (_, currentData) := arr[idx]!
      if currentData.isEmpty then
        logWarning m! "[Lean2TeX] '{boxName}' 已经全部导出"
      else
        let finalJson := Json.arr currentData
        IO.FS.writeFile file.getString finalJson.pretty
        latexExportState.set (arr.set! idx (boxName, #[]))
        logInfo m! "[Lean2TeX] 成功从 '{boxName}' 导出 {currentData.size} 条记录到 {file.getString}"
    | none =>
      logWarning m! "[Lean2TeX] '{boxName}' 不存在"
