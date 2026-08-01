import Lean2TeX.Prelude

namespace Lean2TeX.Pipeline


mutual

  /-- A node in the proof AST. -/
  inductive PNode where
    /-- A `theorem` / `lemma` declaration -/
    | pRoot
      (name : String)
      (raw : String)
      (steps : List PNode)
    /-- An ordinary tactic matched by a config rule. -/
    | pTactic
      (name : String)
      (args : List (String × String))
      (put_off : Bool)
      (raw : String)
    /-- `have ... := by ...` -/
    | pHave
      (raw : String)
      (proof : List PNode)
    /-- A `calc` block -/
    | pCalc
      (raw : String)
      (rawSteps : List String)
    /-- A contradiction goal introduced by `intro` / `by_contra` -/
    | pContra
      (raw : String)
      (arg : String)
      (proof : List PNode)
    /-- `cases` / `induction` / `rcases` with named branches. -/
    | pCases
      (name : String)
      (raw : String)
      (branches : List PBranch)
    /-- Others -/
    | pUnknown
      (raw : String)

  /-- One branch of a `cases` / `induction` / `rcases` node. -/
  inductive PBranch where
    | mk (raw : String) (body : List PNode) (label : String := "")

end


end Lean2TeX.Pipeline
