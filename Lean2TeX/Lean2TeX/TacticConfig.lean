import Lean2TeX.Prelude

open Lean2TeX
open Lean

namespace Lean2TeX


/-! # Tactic Configuration System -/

/-- Specifies how to extract an argument from a matched tactic's syntax tree.
    Each captured identifier is recorded in the JSON output under the given `label`. -/
structure TacticArgSpec where
  /-- 0-based index into the list of `ident` nodes collected from the tactic's
      syntax tree (depth-first, left-to-right). -/
  identIndex : Nat
  /-- Label used as the JSON key for this argument in the recorder output. -/
  label : String
  deriving Repr, BEq, Inhabited

structure TacticConfig where
  name : String
  /-- `true` = match by Lean syntax kind (`tac.raw.getKind`).
      `false` = match by tactic source text. -/
  kind : Bool
  /-- The string to match against.
      - When `kind = true`: compared against `tac.raw.getKind.toString` after
        stripping the `Lean.Parser.Tactic.` prefix (e.g. `"exact"`, `"normNum"`).
      - When `kind = false`: compared against the tactic's source text,
        controlled by `prefix_match`. -/
  pattern : String
  /-- If `false`, the `pattern` is __exactly__ matched (used for single-token
      tactics like `rfl`, `sorry`).  Default `true` (prefix match). -/
  prefix_match : Bool := true
  /-- If `true`, the recorder is inserted __after__ the tactic
      (for tactics that introduce new bindings, like `obtain`, `have`). -/
  put_off : Bool := false
  /-- Argument extraction specs: which `ident` children to capture from the
      syntax tree, and what JSON key to label them with. -/
  args : List TacticArgSpec := []
  /-- Labels of arguments that should be relayed (passed through) to the
      recorder of the *next* tactic step.  Currently used by `unfold` to
      propagate the `at` location. -/
  relayArgs : List String := []
  deriving Repr, BEq, Inhabited


/-! # Built-in Tactic Configurations -/

def builtinTacticConfigs : List TacticConfig := [
  -- kind=true: match by Lean syntax kind
  { name := "exact",
    kind := true,
    pattern := "exact" },
  { name := "apply",
    kind := true,
    pattern := "apply" },
  { name := "change",
    kind := true,
    pattern := "change" },
  { name := "unfold",
    kind := true,
    pattern := "unfold",
    args := [ { identIndex := 0, label := "concept" },
              { identIndex := 1, label := "at" } ],
    relayArgs := ["at"] },
  { name := "obtain", kind := false, pattern := "obtain", prefix_match := true, put_off := true },
  { name := "have",   kind := true,  pattern := "tacticHave__", put_off := true },
  -- kind=false: match by tactic source text (all verified working in core Lean 4)
  { name := "intro",      kind := false, pattern := "intro",      prefix_match := true },
  { name := "intros",     kind := false, pattern := "intros",     prefix_match := true },
  { name := "refine",     kind := false, pattern := "refine",     prefix_match := true },
  { name := "constructor",kind := false, pattern := "constructor",prefix_match := true },
  { name := "left",       kind := false, pattern := "left",       prefix_match := false },
  { name := "right",      kind := false, pattern := "right",      prefix_match := false },
  { name := "assumption", kind := false, pattern := "assumption", prefix_match := false },
  { name := "trivial",    kind := false, pattern := "trivial",    prefix_match := false },
  { name := "rw",         kind := false, pattern := "rw",         prefix_match := true },
  { name := "simp",       kind := false, pattern := "simp",       prefix_match := true },
  { name := "dsimp",      kind := false, pattern := "dsimp",      prefix_match := true },
  { name := "by_cases",   kind := false, pattern := "by_cases",   prefix_match := true },
  { name := "induction",  kind := false, pattern := "induction",  prefix_match := true },
  { name := "decide",     kind := false, pattern := "decide",     prefix_match := false },
  { name := "calc",       kind := false, pattern := "calc",       prefix_match := true },
  { name := "exfalso",    kind := false, pattern := "exfalso",    prefix_match := false },
  { name := "omega",      kind := false, pattern := "omega",      prefix_match := false },
  { name := "gcongr",     kind := false, pattern := "gcongr",     prefix_match := false },
  { name := "rcases",     kind := false, pattern := "rcases",     prefix_match := true },
  { name := "sorry",      kind := false, pattern := "sorry",      prefix_match := false },
  { name := "rfl",        kind := false, pattern := "rfl",        prefix_match := false }
]


/-! # Persistent Environment Extension -/

initialize tacticConfigsExt : SimplePersistentEnvExtension TacticConfig (List TacticConfig) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun configs config => configs ++ [config]
    addImportedFn := fun es =>
      mkStateFromImportedEntries (fun configs config => configs ++ [config]) builtinTacticConfigs es
  }


/-! # Syntax Tree Utilities -/

/-- Collect ident nodes, preserving the full Syntax so they can be used as
    `TSyntax ident` in antiquotation. -/
partial def collectIdentStxs (stx : Syntax) : List Syntax :=
  match stx with
  | .ident _ _ _ _ => [stx]
  | _ => (stx.getArgs.toList.map collectIdentStxs).foldr (· ++ ·) []

partial def extractTacticText (stx : Syntax) : String :=
  match stx with
  | .atom _ val =>
    let t := val.trimAscii.toString
    if t.isEmpty then "" else t
  | .ident _ _ id _ => id.toString
  | _ =>
    let parts := (stx.getArgs.toList.map extractTacticText).filter (!·.isEmpty)
    (" ".intercalate parts).trimAscii.toString


/-! # Matching Logic -/

def matchByKind (rawKind : String) (config : TacticConfig) : Option (String × Bool) :=
  let shortKind := if rawKind.startsWith "Lean.Parser.Tactic." then rawKind.drop 19 else rawKind
  if shortKind == config.pattern then
    some (config.name, config.put_off)
  else none

def matchByText (tacText : String) (config : TacticConfig) : Option (String × Bool) :=
  let s := tacText.trimAscii.toString
  if config.prefix_match then
    if s.startsWith config.pattern then some (config.name, config.put_off) else none
  else
    if s == config.pattern then some (config.name, config.put_off) else none

/-- Try matching a single config entry. Returns `some (name, args, isAfter)` or `none`.
    `args` carries `Syntax` nodes from the original tactic, preserving
    source info for antiquotation. -/
def tryMatchConfig (rawKind : String) (tacText : String) (tac : TSyntax `tactic) (config : TacticConfig)
    : Option (String × Array (Syntax × String) × Bool) :=
  if config.kind then
    match matchByKind rawKind config with
    | some (name, isAfter) =>
      let stxs := collectIdentStxs tac.raw
      let args : Array (Syntax × String) :=
        config.args.toArray.filterMap fun argSpec =>
          if argSpec.identIndex < stxs.length then
            some (stxs[argSpec.identIndex]!, argSpec.label)
          else none
      some (name, args, isAfter)
    | none => none
  else
    match matchByText tacText config with
    | some (name, isAfter) => some (name, #[], isAfter)
    | none => none

/-- Core tactic parser: matches `tac` against `configs`. Pure function.
    Returns `(recorder_name, extracted_syntax_nodes, insert_after?)`. -/
def parseTacticConfig (configs : List TacticConfig) (tac : TSyntax `tactic)
    : (String × Array (Syntax × String) × Bool) :=
  let rawKind := tac.raw.getKind.toString
  let tacText := extractTacticText tac.raw
  match configs.findSome? (tryMatchConfig rawKind tacText tac) with
  | some result => result
  | none =>
    let name := if rawKind.startsWith "Lean.Parser.Tactic." then rawKind.drop 19 else rawKind
    (name.toString, #[], false)


/-! # JSON Parsing for External Config Files -/

def parseTacticConfigFromJson (j : Json) : Except String TacticConfig := do
  let name ← j.getObjValAs? String "name"
  let kind ← j.getObjValAs? Bool "kind"
  let pattern ← j.getObjValAs? String "pattern"
  let put_off := (j.getObjValAs? Bool "put_off").toOption.getD false
  let prefix_match := (j.getObjValAs? Bool "prefix_match").toOption.getD true
  let argsArr : Array Json := (j.getObjValAs? (Array Json) "args").toOption.getD #[]
  let relayArr : Array Json := (j.getObjValAs? (Array Json) "relayArgs").toOption.getD #[]

  let args : List TacticArgSpec :=
    (argsArr.toList.reverse).filterMap fun argJson =>
      match Json.getObjValAs? argJson Nat "identIndex", Json.getObjValAs? argJson String "label" with
      | .ok idx, .ok lbl => some { identIndex := idx, label := lbl }
      | _, _ => none

  let relayArgs : List String :=
    (relayArr.toList.reverse).filterMap fun r =>
      match r.getStr? with
      | .ok s => some s
      | .error _ => none

  return {
    name := name, kind := kind, pattern := pattern,
    prefix_match := prefix_match, put_off := put_off,
    args := args, relayArgs := relayArgs
  }

def parseTacticConfigsFromJson (j : Json) : Except String (List TacticConfig) := do
  let arr ← j.getArr?
  let mut configs : List TacticConfig := []
  for elem in arr.toList.reverse do
    let c ← parseTacticConfigFromJson elem
    configs := c :: configs
  return configs

open Elab Command in
elab "#load_tactics" path:str : command => do
  let filePath := path.getString
  let content ← IO.FS.readFile filePath
  match Json.parse content with
  | .error e => throwError s!"[Lean2TeX] Failed to parse JSON in '{filePath}': {e}"
  | .ok json =>
    match parseTacticConfigsFromJson json with
    | .error e => throwError s!"[Lean2TeX] Invalid config in '{filePath}': {e}"
    | .ok configs =>
      let env ← getEnv
      let mut newEnv := env
      for config in configs do
        newEnv := tacticConfigsExt.addEntry newEnv config
      setEnv newEnv
      logInfo m!"[Lean2TeX] Loaded {configs.length} tactic config(s) from '{filePath}'"

end Lean2TeX
