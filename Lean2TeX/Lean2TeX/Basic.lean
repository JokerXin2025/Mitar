import Lean
import Mathlib.Data.Real.Basic

export Lean (Name Expr Json MetaM Meta.inferType)

inductive TeXStyle where
  | Root
  | Basic
  | Def
  | Plain
  | Fancy
  | Mathbb
  | Mathbf
  deriving Repr, BEq
export TeXStyle (Basic Def Plain Fancy Mathbb Mathbf)

abbrev ExprRecFunc := Expr → TeXStyle → MetaM String
abbrev Rule := Expr → ExprRecFunc → MetaM (Option String)

initialize JSON_boxes : IO.Ref (Array (Name × Array Json)) ← IO.mkRef #[]
