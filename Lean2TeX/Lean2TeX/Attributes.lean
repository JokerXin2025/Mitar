import Lean2TeX.Prelude

open Lean2TeX
open Lean

declare_syntax_cat identList
syntax "[" ident,* "]" : identList

declare_syntax_cat configItem
syntax "target_display" ":=" ident : configItem
syntax "args_display" ":=" "[" identList,* "]" : configItem
syntax "args_context_node" ":=" "[" ident,* "]" : configItem

syntax (name := Lean2TeX) "Lean2TeX" ppSpace str ppSpace ident (ppSpace "(" ppSpace configItem,* ")")? : attr

initialize Templates : MapDeclarationExtension TemplateData ← mkMapDeclarationExtension
initialize
  registerBuiltinAttribute {
    name := `Lean2TeX
    descr := "Lean2TeX Templates with Configurations"
    add := fun declName stx attrKind => do
      match stx with
      | `(attr| Lean2TeX $template:str $node:ident $[($items,*)]?) =>
        let mut config : TemplateConfig := {}
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
            | `(configItem| args_context_node := [$ns,*]) =>
                let nTypes ← ns.getElems.toList.mapM (fun n => parseNodeType n.getId)
                config := { config with ArgsContextNode := nTypes }
            | _ => throwError "Invalid configuration item syntax"
        let data := {
          template := template.getString
          node := ← parseNodeType node.getId
          config := config
        }
        setEnv (Templates.insert (← getEnv) declName data)
      | _ => throwError "Invalid Lean2TeX attribute syntax"
  }
