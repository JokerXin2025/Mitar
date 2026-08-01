import Lean2TeX.Pipeline.AST
import Lean2TeX.Pipeline.Rules

namespace Lean2TeX.Pipeline


/-! # Small text helpers -/

/-- Number of leading spaces in a line. -/
def indentOf (line : String) : Nat :=
  line.length - line.trimAsciiStart.length

/-- `n` spaces. -/
def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

/-- Split a line into whitespace-separated words. -/
def words (line : String) : List String :=
  (line.trimAscii.toString.splitOn " ").filter (!·.isEmpty)

/-- Convert a camelCase name to snake_case (`normNum` → `norm_num`).
    Kind-based configs store the Lean syntax-kind name; at the text level
    we must match the tactic's snake_case spelling. -/
def camelToSnake (s : String) : String :=
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
        if c.isUpper && !acc.isEmpty then go rest (c.toLower :: '_' :: acc)
        else go rest (c.toLower :: acc)
  String.ofList (go s.toList [])

/-- Safe list indexing: `get? list n = some x` iff `list[n] = x`. -/
def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n


/-! # Tactic matching -/

/-- Find the first config that matches the line text.
    Returns `(name, putOff, args)` where args are `(value, label)` pairs.
    Kind-based entries (e.g. `norm_num`) also match their pattern followed by
    arguments (`norm_num at h_m`), since at the text level we cannot see
    syntax kinds. -/
def matchTactic (rules : PipelineRules) (line : String) : Option (String × Bool × List (String × String)) :=
  let s := line.trimAscii.toString
  rules.tacticConfigs.findSome? fun cfg =>
    let matched := if cfg.kind then
        let snake := camelToSnake cfg.pattern
        s == snake || s.startsWith (snake ++ " ")
      else if cfg.prefix_match then s.startsWith cfg.pattern else s == cfg.pattern
    if !matched then none
    else
      let argValues := words s |>.drop 1
      -- Skip words listed in `relayArgs` (e.g. the `at` in `unfold a at h_m`):
      -- they are Lean keyword-like tokens that cannot appear as recorder
      -- `ident` arguments (and carry no information we want to record).
      let args : List (String × String) := cfg.args.filterMap fun spec =>
        match listGet? argValues spec.identIndex with
        | some v => if cfg.relayArgs.contains v then none else some (v, spec.label)
        | none => none
      some (cfg.name, cfg.put_off, args)

/-- Classify a single line into a `PNode` (non-structural). -/
def classifyLine (rules : PipelineRules) (line : String) : PNode :=
  match matchTactic rules line with
  | some (name, putOff, args) => PNode.pTactic name args putOff line
  | none => PNode.pUnknown line

/-- Try to extract a human-readable branch label from the branch line.
    e.g. `| zero => ...` → `zero`; `· ...` → `case <n>` (assigned later). -/
def extractBranchLabel (sr : StructuralRule) (trimmed : String) : String :=
  let afterMarker := trimmed.dropWhile (fun c => c != '|' && c != '·' && c != ' ')
  let rest := afterMarker.trimAscii.toString.dropWhile (fun c => c == '|' || c == '·') |>.trimAscii.toString
  let withoutArrow := (rest.splitOn "=>").getD 0 "" |>.trimAscii.toString
  if withoutArrow.isEmpty then "" else withoutArrow.splitOn " " |>.getD 0 ""

/-! # Block parsing (mutually recursive with branch parsing) -/

mutual
  /-- Collect consecutive lines that are indented deeper than `minIndent`.
      Used for `calc` step bodies and branch bodies. -/
  partial def collectIndented (lines : Array String) (start : Nat) (minIndent : Nat)
      : List String × Nat :=
    let rec go (i : Nat) (acc : List String) : List String × Nat :=
      if i >= lines.size then (acc.reverse, i)
      else
        let line := lines[i]!
        if line.trimAscii.isEmpty then go (i + 1) acc
        else if indentOf line > minIndent then go (i + 1) (line :: acc)
        else (acc.reverse, i)
    go start []

  /-- Parse a block of lines: consume lines starting at `start`, stopping
      when a line has indentation strictly less than `basicIndent`. -/
  partial def parseBlock (lines : Array String) (start : Nat) (basicIndent : Nat)
      (rules : PipelineRules) : List PNode × Nat :=
    let rec loop (i : Nat) (acc : List PNode) : List PNode × Nat :=
      if i >= lines.size then (acc.reverse, i)
      else
        let line := lines[i]!
        let ind := indentOf line
        if ind < basicIndent then (acc.reverse, i)
        else if line.trimAscii.isEmpty then loop (i + 1) acc
        else
          -- Calc block
          if line.trimAscii == "calc" then
            let (rawSteps, nextI) := collectIndented lines (i + 1) (ind + 1)
            loop nextI (PNode.pCalc line rawSteps :: acc)
          else
            let trimmed := line.trimAscii.toString
            -- `have ... := by ...` → NewGoal
            if trimmed.startsWith "have " && trimmed.contains ":=" && trimmed.contains "by" then
              let (steps, nextI) := parseBlock lines (i + 1) (ind + 1) rules
              loop nextI (PNode.pHave line steps :: acc)
            else
              -- `intro x` / `by_contra x` → Contra
              let contraArg :=
                if trimmed.startsWith "intro " then some (words trimmed |>.getD 1 "")
                else if trimmed.startsWith "by_contra " then some (words trimmed |>.getD 1 "")
                else none
              match contraArg with
              | some arg =>
                  -- `intro x` / `by_contra x` opens a contradiction goal; the
                  -- following tactics at the *same* indentation belong to it
                  -- (unlike `have`, whose proof must be deeper).  So collect
                  -- with `basicIndent := ind`, not `ind + 1`.
                  let (steps, nextI) := parseBlock lines (i + 1) ind rules
                  loop nextI (PNode.pContra line arg steps :: acc)
              | none =>
                  -- Structural tactics (cases/induction/rcases/...)
                  let structural := rules.structural.findSome? fun sr =>
                    if trimmed.startsWith sr.name then some sr else none
                  match structural with
                  | some sr =>
                      let (branches, nextI) := parseBranches lines (i + 1) ind sr rules
                      loop nextI (PNode.pCases sr.name line branches :: acc)
                  | none =>
                      let node := classifyLine rules line
                      loop (i + 1) (node :: acc)
    loop start []

  /-- For `cases`/`induction`/`rcases`, branches start with a marker
      (`|` or `·`) at the same indentation as the tactic.  Each branch
      body is parsed with `parseBlock`.  Single-line branches
      (`| pat => tac; tac`) have their body inline after `=>`. -/
  partial def parseBranches (lines : Array String) (start : Nat) (baseIndent : Nat)
      (sr : StructuralRule) (rules : PipelineRules) : List PBranch × Nat :=
    let rec go (i : Nat) (acc : List PBranch) : List PBranch × Nat :=
      if i >= lines.size then (acc.reverse, i)
      else
        let line := lines[i]!
        let ind := indentOf line
        if ind < baseIndent then (acc.reverse, i)
        else
          let trimmed := line.trimAscii.toString
          let isBranch := sr.markers.any (fun m => trimmed.startsWith m)
          if !isBranch then
            (acc.reverse, i)
          else
            -- Split branch marker from any inline body.
            --   `· tac`          → header `·`, body `tac`
            --   `| pat => tac`   → header `| pat =>`, body `tac`
            -- The inline body is re-indented to (branch indent + 2) and
            -- parsed as the first body line, so recorders can be inserted.
            let isBullet := trimmed.startsWith "·"
            let (headerPart, inlineBody) := if isBullet then
              ("·", (trimmed.drop 1).trimAscii.toString)
            else
              let parts := trimmed.splitOn "=>"
              match parts with
              | h :: _ =>
                  let header := h.trimAscii.toString ++ "=>"
                  let body := parts.drop 1 |>.foldl (fun a b => if a.isEmpty then b else a ++ "=>" ++ b) ""
                  (header, body.trimAscii.toString)
              | [] => (trimmed, "")
            if inlineBody.isEmpty then
              -- Multi-line branch: collect indented lines below.
              let (bodyLines, nextI) := collectIndented lines (i + 1) ind
              let body := parseBlock bodyLines.toArray 0 (indentOf line + 1) rules |>.1
              let label := extractBranchLabel sr trimmed
              go nextI (PBranch.mk line body label :: acc)
            else
              -- Single-line branch: split marker from body, keep original
              -- indentation of the deeper lines (nested proofs stay valid).
              let bodyHead := spaces (ind + 2) ++ inlineBody
              let (deeper, nextI) := collectIndented lines (i + 1) ind
              let body := parseBlock (bodyHead :: deeper).toArray 0 (ind + 2) rules |>.1
              let headerLine := spaces ind ++ headerPart
              let label := extractBranchLabel sr trimmed
              go nextI (PBranch.mk headerLine body label :: acc)
    go start []

end


/-! # Theorem block extraction -/

/-- Find the start index of the line containing `#Lean2TeX theorem <name>`. -/
def findTheoremStart (lines : Array String) (name : String) : Option Nat :=
  let marker := s!"#Lean2TeX theorem {name}"
  lines.findIdx? (fun l => l.contains marker)

/-- Extract the theorem block: from the start line up to (not including)
    the next top-level (indent 0) non-blank line. -/
partial def extractTheoremBlock (lines : Array String) (start : Nat) : List String :=
  let rec go (i : Nat) (acc : List String) : List String :=
    if i >= lines.size then acc.reverse
    else
      let line := lines[i]!
      if i > start && indentOf line == 0 && !line.trimAscii.isEmpty then acc.reverse
      else go (i + 1) (line :: acc)
  go start []

/-- Split source lines into (header-lines, body-lines) starting at `startIdx`.
    The header ends at the line containing `:= by`; the body continues until
    the next top-level (indent 0) non-blank line. -/
partial def splitAtBy (lines : Array String) (startIdx : Nat) : List String × List String :=
  goHeader startIdx []
where
  collectBody (lines : Array String) (start : Nat) : List String :=
    let rec go (i : Nat) (acc : List String) : List String :=
      if i >= lines.size then acc.reverse
      else
        let l := lines[i]!
        if indentOf l == 0 && !l.trimAscii.isEmpty then acc.reverse
        else go (i + 1) (l :: acc)
    go start []
  goHeader (i : Nat) (header : List String) : List String × List String :=
    if i >= lines.size then (header.reverse, [])
    else
      let l := lines[i]!
      if l.contains ":=" && l.contains "by" then
        ((l :: header).reverse, collectBody lines (i + 1))
      else
        goHeader (i + 1) (l :: header)

end Lean2TeX.Pipeline
