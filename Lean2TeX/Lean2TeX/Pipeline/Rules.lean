import Lean
import Lean2TeX.TacticConfig

open Lean

namespace Lean2TeX.Pipeline


/-- A structural tactic: one whose proof body contains named branches
    (`| zero =>`, `· ...`) that must be recursively parsed. -/
structure StructuralRule where
  name : String
  /-- Characters that introduce a branch line (`|` for pipe syntax,
      `·` for bullet syntax). -/
  markers : List String
  deriving Repr, BEq, Inhabited

/-- An indentation rule for branch bodies: branch lines are indented
    relative to the tactic line by this many spaces (default 2). -/
structure IndentRule where
  branchIndent : Nat := 2
  deriving Repr, BEq, Inhabited

/-- Calc relation symbol → TeX rendering. -/
structure CalcRelation where
  symbol : String
  tex : String
  deriving Repr, BEq, Inhabited

/-- The full set of rules the text pipeline uses. -/
structure PipelineRules where
  /-- Tactic configs (built-in + loaded via `#load_tactics`). -/
  tacticConfigs : List TacticConfig := []
  /-- Structural tactics (cases/induction/rcases/...). -/
  structural : List StructuralRule := []
  /-- Indentation conventions. -/
  indent : IndentRule := {}
  /-- Calc relation mappings. -/
  calcRelations : List CalcRelation := []
  deriving Repr, Inhabited


/-! ## Persistent environment extension -/

initialize pipelineRulesExt : SimplePersistentEnvExtension PipelineRules (List PipelineRules) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun rules r => rules ++ [r]
    addImportedFn := fun es =>
      mkStateFromImportedEntries (fun rules r => rules ++ [r]) [] es
  }

/-! ## JSON parsing -/

def parseStructuralFromJson (j : Json) : Except String StructuralRule := do
  let name ← j.getObjValAs? String "name"
  let markersArr : Array Json := (j.getObjValAs? (Array Json) "markers").toOption.getD #[]
  let markers := (markersArr.toList.reverse).filterMap (·.getStr?.toOption)
  return { name := name, markers := markers }

def parseCalcFromJson (j : Json) : Except String (List CalcRelation) := do
  let obj ← j.getObj?
  let mut out := []
  for (key, val) in obj.toList do
    match val.getStr? with
    | .ok tex => out := { symbol := key, tex := tex } :: out
    | .error _ => pure ()
  return out.reverse

/-- Parse the pipeline rules from a JSON object.
    `tacticConfigs` is passed separately (it comes from the env extension). -/
def parsePipelineRulesFromJson (j : Json) (tacticConfigs : List TacticConfig) : Except String PipelineRules := do
  let structuralArr : Array Json := (j.getObjValAs? (Array Json) "structural").toOption.getD #[]
  let structural := (structuralArr.toList.reverse).filterMap fun e =>
    match parseStructuralFromJson e with | .ok r => some r | .error _ => none
  let calcArr := j.getObjVal? "calc_relations"
  let calcRelations : List CalcRelation :=
    match calcArr with
    | .ok obj =>
        match obj.getObj? with
        | .ok pairsMap =>
            pairsMap.toList.filterMap fun (k, v) =>
              match v.getStr? with | .ok tex => some { symbol := k, tex := tex } | .error _ => none
        | .error _ => []
    | .error _ => []
  return { tacticConfigs := tacticConfigs, structural := structural, calcRelations := calcRelations }

/-- Load pipeline rules from a JSON file (with tactic configs from env).
    Stores the parsed rules in a persistent environment extension. -/
elab "#load_pipeline_rules" path:str : command => do
  let filePath := path.getString
  let content ← IO.FS.readFile filePath
  match Json.parse content with
  | .error e => throwError s!"[Lean2TeX] Failed to parse JSON in '{filePath}': {e}"
  | .ok json =>
    let env ← getEnv
    let tacticConfigs := tacticConfigsExt.getState env
    match parsePipelineRulesFromJson json tacticConfigs with
    | .error e => throwError s!"[Lean2TeX] Invalid pipeline rules in '{filePath}': {e}"
    | .ok rules =>
      setEnv (pipelineRulesExt.addEntry env rules)
      logInfo m!"[Lean2TeX] Loaded pipeline rules from '{filePath}': {rules.structural.length} structural, {rules.calcRelations.length} calc relations"


end Lean2TeX.Pipeline
