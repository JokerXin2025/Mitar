import Lean
import Batteries.Lean.Expr

export Lean (Name Expr Json MetaM)
export Lean.Meta (isProp inferType)

namespace Lean2TeX

inductive TeXStyle where
  | Root
  | Basic
  | Def
  | Symbol
  | Word
  | Plain
  | Fancy
  | Mathbb
  | Mathbf
  deriving Repr, BEq

inductive OperNode where
  | Text
  | Unit
  | Rel
  | Implies
  | Supscript
  | Subscript
  | App
  | BracApp
  | Display
  | MultiLine
  | Add
  | Minus
  | Mul
  | Frac
  | Abs
  deriving Repr, BEq

abbrev NodeInfo := String × OperNode
abbrev ExprRecFunc := Expr → OperNode → TeXStyle → MetaM String
abbrev ExprPassFunc := Array Expr → Expr → MetaM String
abbrev Rule := Expr → ExprRecFunc → MetaM (Option NodeInfo)
abbrev MetaRule := Expr → OperNode → TeXStyle → ExprRecFunc → MetaM (Option NodeInfo)

initialize JSON_boxes : IO.Ref (Array (Name × Array Json)) ← IO.mkRef #[]

end Lean2TeX
