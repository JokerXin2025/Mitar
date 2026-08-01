import Lean2TeX.Core
import Lean2TeX.Tactics
import Lean2TeX.Pipeline.AST
import Lean2TeX.Pipeline.Rules
import Lean2TeX.Pipeline.Parser
import Lean2TeX.Pipeline.Rewriter
import Lean2TeX.TacticConfig

open Lean Elab Command Term
open Lean2TeX
open Lean2TeX.Pipeline

/-! ============================================================
# Commands

## `#Lean2TeX theorem`
Text-level instrumentation pipeline:

1. Read the current source file (`IO.FS.readFile`).
2. Extract the `#Lean2TeX theorem <name>` block from the text.
3. Parse the proof body into an AST (`Pipeline.Parser`).
4. Rewrite it, generating `Lean2TeX` recorder text lines
   (`Pipeline.Rewriter`).
5. Assemble a `def` command and re-parse it with
   `Parser.runParserCategory` — this is what makes the generated
   recorder tactics *actually execute* (text-level rewrite avoids
   the macro-hygiene issues of the old Syntax-tree approach).
6. `elabCommand` the re-parsed command, then export the JSON.

## `Lean2TeX box => file`
Export a JSON box to a file.
============================================================ -/

/-! ## Default structural rules (softened; overridable via `#load_pipeline_rules`) -/

def defaultStructuralRules : List StructuralRule := [
  { name := "cases", markers := ["|"] },
  { name := "induction", markers := ["|"] },
  { name := "rcases", markers := ["·"] }
]

/-! ## JSON export command -/

/-- Export JSON box into a JSON file. -/
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


/-! ## `#Lean2TeX theorem` — text-level instrumentation -/

syntax (name := lean2texCmd) "#Lean2TeX" "theorem" ident (bracketedBinder)* ":" term ":=" "by" tacticSeq : command

elab_rules : command
| `(command| #Lean2TeX theorem $id:ident $[$bs:bracketedBinder]* : $ty:term := by $seq:tacticSeq) => do
  let env ← getEnv
  let configs := tacticConfigsExt.getState env
  -- Use pipeline rules loaded via `#load_pipeline_rules` if any,
  -- otherwise fall back to the built-in defaults.
  let loadedRules := pipelineRulesExt.getState env
  let rules : PipelineRules := match loadedRules.getLast? with
    | some r => r
    | none => { tacticConfigs := configs, structural := defaultStructuralRules }

  -- Phase 1: read the source file
  let fileName ← getFileName
  let content ← IO.FS.readFile fileName
  let lines := content.splitOn "\n" |>.toArray

  -- Phase 2: locate the theorem block
  let thmName := id.getId.toString
  match findTheoremStart lines thmName with
  | none => throwError m!"[Lean2TeX] Cannot find '#Lean2TeX theorem {thmName}' in {fileName}"
  | some startIdx =>
      -- Phase 3: split header from proof body at `:= by`
      let (headerLines, bodyLines) := splitAtBy lines startIdx
      let bodyLinesArr := bodyLines.toArray

      -- Phase 4: parse + rewrite the body
      let (steps, _) := parseBlock bodyLinesArr 0 0 rules
      let (instrumented, _) := (emitSteps steps thmName).run 0

      -- Phase 5: assemble the `def` command from the *original* header text
      -- `#Lean2TeX theorem name ... := by` → `def name ... := by`
      -- Body lines keep their original indentation (text-level rewriting
      -- preserves the source layout; recorders are padded by the Rewriter).
      let firstLine := (headerLines.getD 0 "").replace "#Lean2TeX " "" |>.replace "theorem" "def"
      let firstLine := (firstLine.splitOn ":=").getD 0 "" |>.trimAscii.toString
      let dataBox := "Lean2TeX_Data"
      let defText := firstLine ++ " := by\n" ++
        "\n".intercalate instrumented ++ "\n" ++
        s!"  Lean2TeX vals {dataBox} <- &{thmName}"
      let exportText := s!"Lean2TeX {dataBox} => \"{thmName}_Lean2TeX.json\""

      -- Phase 6: re-parse and elaborate each command separately
      match Parser.runParserCategory env `command defText with
      | .error e =>
          logInfo m!"[Lean2TeX] === defText for {thmName} ===\n{defText}"
          throwError m!"[Lean2TeX] Failed to re-parse instrumented def:\n{e}"
      | .ok stx =>
          elabCommand stx
          match Parser.runParserCategory env `command exportText with
          | .error e => throwError m!"[Lean2TeX] Failed to re-parse export command:\n{e}"
          | .ok stx2 => elabCommand stx2
