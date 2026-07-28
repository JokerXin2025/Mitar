import Lean

export Lean (Name Expr Json MetaM CoreM FVarId)
export Lean.Meta (isProp inferType)

namespace Lean2TeX


inductive DisplayType where
  | Root
  | Basic
  | Def             -- only once
  | Symbol
  | Word
  | Plain
  | Fancy
  | Mathbb
  | Mathbf
  deriving Repr, BEq, Inhabited

instance : ToString DisplayType where
  toString type := ((reprStr type).splitOn ".").getLast!

def parseDisplayType (style : Name) : CoreM DisplayType := do
  match style with
  | `Root => return .Root
  | `Basic => return .Basic
  | `Def => return .Def
  | `Symbol => return .Symbol
  | `Word => return .Word
  | `Plain => return .Plain
  | `Fancy => return .Fancy
  | `Mathbb => return .Mathbb
  | `Mathbf => return .Mathbf
  | _ => throwError "Unknown DisplayType: {style}"

inductive NodeType where
  | UnknownType
  | Text
  | Display
  | Unit
  | Supscript
  | Subscript
  | App
  | BracApp
  | Expr
  | MultiLine
  | Add
  | Minus
  | Mul
  | Frac
  | Abs
  | Rel
  | Implies
  deriving Repr, BEq, Inhabited

instance : ToString NodeType where
  toString type := ((reprStr type).splitOn ".").getLast!

def parseNodeType (node : Name) : CoreM NodeType := do
  match node with
  | `UnknownType => return .UnknownType
  | `Text => return .Text
  | `Display => return .Display
  | `Unit => return .Unit
  | `Supscript => return .Supscript
  | `Subscript => return .Subscript
  | `App => return .App
  | `BracApp => return .BracApp
  | `Expr => return .Expr
  | `MultiLine => return .MultiLine
  | `Add => return .Add
  | `Minus => return .Minus
  | `Mul => return .Mul
  | `Frac => return .Frac
  | `Abs => return .Abs
  | `Rel => return .Rel
  | `Implies => return .Implies
  | _ => throwError "Unknown NodeType: {node}"

inductive NodeRole where
  | only
  | left
  | right
  | base
  | script
  | numerator
  | denominator
  | lower
  | upper
  | operand
  | func
  | func_arg
  deriving Repr, BEq, Inhabited

structure TemplateConfig where
  TargetDisplay   : DisplayType := .Basic
  ArgsDisplay     : List (List DisplayType) := []
  ArgsContextNode : List NodeType := []
  deriving Repr, Inhabited

structure TemplateData where
  template  : String
  node      : NodeType
  config    : TemplateConfig := {}
  deriving Repr, Inhabited

abbrev NodeInfo :=
  String × NodeType
abbrev ExprRecFunc :=
  Expr → NodeType → NodeRole → List DisplayType → List (FVarId × String)
  → MetaM String
abbrev Rule :=
  Expr → ExprRecFunc → List DisplayType → List (FVarId × String)
  → MetaM (Option NodeInfo)

initialize JSON_boxes : IO.Ref (Array (Name × Array Json)) ← IO.mkRef #[]
initialize Var_Usages : IO.Ref (Array (String × Array Bool)) ← IO.mkRef #[]

end Lean2TeX


/-! Utilities Copied From `Batteries` -/

def Lean.Expr.getAppArgs' (e : Expr) : Array Expr :=
  let dummy := mkSort .zero
  let nargs := e.getAppNumArgs'
  go e (.replicate nargs dummy) (nargs - 1)
where
  go : Expr → Array Expr → Nat → Array Expr
    | mdata _ b, as, i => go b as i
    | app f a  , as, i => go f (as.set! i a) (i-1)
    | _        , as, _ => as
