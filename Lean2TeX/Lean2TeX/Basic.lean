import Lean

export Lean (Expr MetaM Meta.inferType)

abbrev Rule := Expr → (Expr → MetaM String) → MetaM (Option String)
