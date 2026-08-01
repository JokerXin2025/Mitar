import Lean2TeX.Prelude

open Lean2TeX
open Lean

declare_syntax_cat identList
syntax "[" ident,* "]" : identList

declare_syntax_cat configItem
syntax "target_display" ":=" ident : configItem
syntax "args_display" ":=" "[" identList,* "]" : configItem

syntax (name := Lean2TeX) "Lean2TeX" ppSpace str ppSpace ident ppSpace ident* (ppSpace "(" ppSpace configItem,* ")")? : attr

syntax (name := Lean2TeX_unwrap) "Lean2TeX_unwrap" ppSpace num : attr

initialize Templates : SimplePersistentEnvExtension (Name × TemplateData) (NameMap (Array TemplateData)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (declName, data) =>
      let arr := match map.find? declName with
        | some a => a
        | none => #[]
      map.insert declName (arr.push data)
    addImportedFn := fun es =>
      mkStateFromImportedEntries (fun map (declName, data) =>
        let arr := match map.find? declName with
          | some a => a
          | none => #[]
        map.insert declName (arr.push data)
      ) {} es
  }

initialize
  registerBuiltinAttribute {
    name := `Lean2TeX
    descr := "Lean2TeX Templates with Configurations"
    add := fun declName stx attrKind => do
      match stx with
      | `(attr| Lean2TeX $template:str $node:ident $roles:ident* $[($items,*)]?) =>
        let mut config : TemplateConfig := {}
        let rTypes ← roles.mapM (fun r => parseNodeRole r.getId)
        config := { config with ArgsRole := rTypes.toList }
        if let some itemsArray := items then
          for item in itemsArray.getElems do
            match item with
            | `(configItem| target_display := $t:ident) =>
                let tType ← parseDisplayType t.getId
                config := { config with TargetDisplay := tType }
            | `(configItem| args_display := [$lists,*]) =>
                let dTypes ← lists.getElems.toList.mapM fun listStx => do
                  match listStx.raw with
                  | `(identList| [$ds,*]) =>
                      ds.getElems.toList.mapM (fun d => parseDisplayType d.getId)
                  | _ => throwError "Invalid inner list syntax in argsDisplay"
                config := { config with ArgsDisplay := dTypes }
            | _ => throwError "Invalid configuration item syntax"
        let data := {
          template := template.getString
          node := ← parseNodeType node.getId
          config := config
        }
        let env ← getEnv
        setEnv (Templates.addEntry env (declName, data))
      | _ => throwError "Invalid Lean2TeX attribute syntax"
  }

initialize UnwrapExt : SimplePersistentEnvExtension (Name × Nat) (NameMap Nat) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun map (declName, idx) => map.insert declName idx
    addImportedFn := fun es =>
      mkStateFromImportedEntries (fun map (declName, idx) => map.insert declName idx) {} es
  }

initialize
  registerBuiltinAttribute {
    name := `Lean2TeX_unwrap
    descr := "Unwrap this constant and directly parse its n-th argument (0-indexed)"
    add := fun declName stx attrKind => do
      match stx with
      | `(attr| Lean2TeX_unwrap $idx:num) =>
        let env ← getEnv
        setEnv (UnwrapExt.addEntry env (declName, idx.getNat))
      | _ => throwError "Invalid Lean2TeX_unwrap attribute syntax"
  }
