import Lean2TeX.Pipeline.AST
import Lean2TeX.Pipeline.Rules
import Lean2TeX.Pipeline.Parser

/-! ============================================================
# Pipeline: Rewriter

Instruments an `AST.PNode` forest by generating `Lean2TeX`
recorder lines, one per step, **preserving the original file's
indentation** (this is the whole point of text-level rewriting:
the output is the source text with recorder lines inserted).

Every emitted recorder line is padded with the indentation of
the tactic line it annotates, so nested structures (branch
bodies, `have` proofs, calc blocks) keep their original layout
and remain valid Lean.

Recorder line patterns (mirroring the Python script):
  goal  : `Lean2TeX {tag} <- _goal_`
  info  : `Lean2TeX {tag} <- "{cfg}" {args}`
  link  : `Lean2TeX {tag} <- "have" &{proofTag}("proof")`
  merge : `Lean2TeX vals {casesTag} <- &{b1} &{b2} ...`
  close : `Lean2TeX {tag} <- "Cases" *{info}("info") &{cases}("cases")`
-/

open Lean

namespace Lean2TeX.Pipeline


/-! ## State

   `GenM` threads a counter used to mint unique recorder tags. -/

abbrev GenM := StateM Nat

/-- Mint a fresh unique index. -/
def freshIdx : GenM Nat := do
  let n ← get
  set (n + 1)
  return n

/-! ## Small helpers -/

/-- Prepend the indentation of `raw` to `s`. -/
def padWith (raw : String) (s : String) : String :=
  spaces (indentOf raw) ++ s

/-- Recorder for the current goal: `Lean2TeX {tag} <- _goal_`. -/
def goalRec (tag : String) : String :=
  s!"Lean2TeX {tag} <- _goal_"

/-- Recorder for a tactic step: `Lean2TeX {tag} <- "{cfg}" args`. -/
def infoRec (tag name : String) (args : List (String × String)) : String :=
  let argsStr := args.foldl (fun acc (v, k) => acc ++ s!" {v}(\"{k}\")") ""
  s!"Lean2TeX {tag} <- \"{name}\"{argsStr}"

/-- Link recorder for a sub-proof: `Lean2TeX {tag} <- "have" &{proofTag}("proof")`. -/
def linkRec (tag kind proofTag : String) : String :=
  s!"Lean2TeX {tag} <- \"{kind}\" &{proofTag}(\"proof\")"

/-- Merge branch arrays: `Lean2TeX vals {casesTag} <- &{b1} &{b2} ...`. -/
def mergeRec (casesTag : String) (branchTags : List String) : String :=
  let refs := branchTags.foldl (fun acc b => acc ++ s!" &{b}") ""
  s!"Lean2TeX vals {casesTag} <-{refs}"

/-- Close recorder for a cases node: `Lean2TeX {tag} <- "Cases" *info &cases`. -/
def casesCloseRec (tag infoTag casesTag : String) : String :=
  s!"Lean2TeX {tag} <- \"Cases\" *{infoTag}(\"info\") &{casesTag}(\"cases\")"

/-! ## Calc step parsing

   Mirrors the Python `__resolve` for `Calc` nodes: each step line
   `<lhs> <rel> <rhs> := <proof>` is turned into `let` bindings plus
   a `Lean2TeX` recorder, and a final link recorder closes the block. -/

/-- Extract the relation symbol from a calc step line. -/
def extractCalcRel (line : String) : String :=
  let rels := ["=? ", "=", "<", ">", "≤", "≥"]
  match rels.findSome? (fun r => if line.contains r then some r else none) with
  | some r => r
  | none => "="

/-- Find the position of substring `sub` in `s`, or `none`.
    Uses `splitOn`: the length of the first part is the match position. -/
def indexOfSubstring (s sub : String) : Option Nat :=
  match s.splitOn sub with
  | first :: rest => if rest.isEmpty then none else some first.length
  | [] => none

/-- Split a calc step line into `(lhs, rhs, proof)`.
    e.g. `a = b := h1` → `("a", "b", "h1")`. -/
def splitCalcStep (line : String) : String × String × String :=
  let trimmed := line.trimAscii.toString
  -- Split off the proof after `:=`
  let parts := trimmed.splitOn ":="
  let expr := match parts with | h :: _ => h.trimAscii.toString | [] => trimmed
  let proof := match parts.drop 1 with | h :: _ => h.trimAscii.toString | [] => ""
  -- Split lhs/rhs at the first relation symbol (search substring)
  let rels := ["=? ", "=", "<", ">", "≤", "≥"]
  let rec findRel (ls : List String) : Option Nat :=
    match ls with
    | [] => none
    | r :: rest =>
        match indexOfSubstring expr r with
        | some pos => some pos
        | none => findRel rest
  match findRel rels with
  | some pos =>
      let lhs := (expr.take pos).toString.trimAscii.toString
      let rhs := (expr.drop (pos + 1)).toString.trimAscii.toString
      (lhs, rhs, proof)
  | none => (expr, "", proof)

/-- Emit recorder lines for a calc block.
    First step: `let _lhs_ := lhs`, `let _rhs1_ := rhs`, recorder.
    Later steps: `let _rhsN_ := rhs`, recorder.
    Inner proof lines (e.g. `ring`, `rw [...]`) are kept verbatim.
    Final: link recorder `Lean2TeX {tag} <- "calc" &{tag}_calc("calc_steps")`.
    All generated lines are padded via `p`. -/
def parseCalcSteps (rawSteps : List String) (tag : String) (p : String → String) : List String :=
  let stepLines := rawSteps.filter (·.contains ":=")
  let (lhs0, rhs0, _) := match stepLines with
    | [] => ("", "", "")
    | s :: _ => splitCalcStep s
  let init := (if lhs0.isEmpty then [] else [p (s!"let _lhs_ := {lhs0}")]) ++
              (if rhs0.isEmpty then [] else [p (s!"let _rhs1_ := {rhs0}")])
  let rec go (steps : List String) (n : Nat) : List String :=
    match steps with
    | [] => []
    | s :: rest =>
        if !s.contains ":=" then
          -- Inner proof line of the calc block (e.g. `ring`); it was
          -- already emitted verbatim with the calc block, so skip here.
          go rest n
        else
          let (_, rhs, _) := splitCalcStep s
          let rel := extractCalcRel s
          let line := if n == 1 then
            [p (s!"Lean2TeX {tag}_calc <- \"{rel}\" _lhs_(\"lhs\") _rhs1_(\"rhs\")")]
          else
            let rhsName := s!"_rhs{n}_"
            [p (s!"let {rhsName} := {rhs}"), p (s!"Lean2TeX {tag}_calc <- \"{rel}\" {rhsName}(\"rhs\")")]
          line ++ go rest (n + 1)
  init ++ go rawSteps 1 ++ [p (s!"Lean2TeX {tag} <- \"calc\" &{tag}_calc(\"calc_steps\")")]

/-! ## Recursion

   `emitNode` produces the instrumented lines for one node.
   The `tag` is the JSON box the node's recorders write to;
   raw source lines are emitted verbatim (keeping indentation),
   and recorder lines are padded with the raw line's indentation. -/

mutual

  partial def emitNode (node : PNode) (tag : String) : GenM (List String) :=
    match node with
    | PNode.pRoot name raw steps => do
        let headerLines := raw.splitOn "\n"
        let stepLines ← emitSteps steps name
        return headerLines ++ stepLines
    | PNode.pTactic name args putOff raw =>
        let p := padWith raw
        let goalLine := p (goalRec tag)
        let infoLine := p (infoRec tag name args)
        if putOff then
          -- `obtain`-style tactics bind new names; record *after* the tactic
          return [goalLine, raw, infoLine]
        else
          return [goalLine, infoLine, raw]
    | PNode.pCalc raw rawSteps =>
        let p := padWith raw
        -- The `let` bindings and recorders come *before* the calc block,
        -- while a goal is still open (`let` fails on zero goals).  The
        -- calc keyword and its steps are then emitted verbatim.
        return [p (goalRec tag)] ++ parseCalcSteps rawSteps tag p ++ [raw] ++ rawSteps
    | PNode.pHave raw proof => do
        let idx ← freshIdx
        let proofTag := s!"{tag}_proof{idx}"
        let proofLines ← emitSteps proof proofTag
        let p := padWith raw
        return [p (goalRec tag), raw] ++ proofLines ++ [p (linkRec tag "have" proofTag)]
    | PNode.pContra raw arg proof => do
        let idx ← freshIdx
        let infoTag := s!"{tag}_info{idx}"
        let proofTag := s!"{tag}_proof{idx}"
        let p := padWith raw
        let setup := p (s!"Lean2TeX {infoTag} <- {arg}(\"h_contra\")")
        let proofLines ← emitSteps proof proofTag
        let close := p (s!"Lean2TeX {tag} <- \"Contradiction\" *{infoTag}(\"info\") &{proofTag}(\"proof\")")
        -- `intro hnp` introduces `hnp`, so setup must come *after* the raw tactic
        return [p (goalRec tag), raw, setup] ++ proofLines ++ [close]
    | PNode.pCases name raw branches => do
        let idx ← freshIdx
        let infoTag := s!"{tag}_info{idx}"
        let casesTag := s!"{tag}_cases{idx}"
        let p := padWith raw
        -- Emit each branch: header line verbatim, then the branch body
        -- (whose own lines already carry their original indentation).
        let mut branchLines := []
        let mut branchTags := []
        for branch in branches.reverse do
          let bIdx ← freshIdx
          let bTag := s!"{tag}_branch{bIdx}"
          branchTags := bTag :: branchTags
          match branch with
          | PBranch.mk header body _ =>
              if body.isEmpty then
                -- Single-line branch (`| pat => tac; tac` or `· tac`):
                -- body is inline in the header; emit the header as-is.
                branchLines := [header] ++ branchLines
              else
                let bodyLines ← emitSteps body bTag
                branchLines := (header :: bodyLines) ++ branchLines
        -- Merge branch arrays and close the cases node
        let merge := p (mergeRec casesTag branchTags)
        let close := p (casesCloseRec tag infoTag casesTag)
        let setup := p (infoRec infoTag name [])
        return [p (goalRec tag), setup, raw] ++ branchLines ++ [merge, close]
    | PNode.pUnknown raw =>
        return [raw]

  partial def emitSteps (steps : List PNode) (tag : String) : GenM (List String) :=
    steps.foldlM (fun acc step => do
      let lines ← emitNode step tag
      return acc ++ lines) []

end


end Lean2TeX.Pipeline
