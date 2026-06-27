import Lean
import Batteries.Lean.Expr

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
  toString
  | .Root => "Root"
  | .Basic => "Basic"
  | .Def => "Def"
  | .Symbol => "Symbol"
  | .Word => "Word"
  | .Plain => "Plain"
  | .Fancy => "Fancy"
  | .Mathbb => "Mathbb"
  | .Mathbf => "Mathbf"

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
    | BySupscript   -- as parent
  | Subscript
    | BySubscript   -- as parent
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
  toString
  | .UnknownType => "UnknownType"
  | .Text => "Text"
  | .Display => "Display"
  | .Unit => "Unit"
  | .Supscript => "Supscript"
    | .BySupscript => "BySupscript"
  | .Subscript => "Subscript"
    | .BySubscript => "BySubscript"
  | .App => "App"
  | .BracApp => "BracApp"
  | .Expr => "Expr"
  | .MultiLine => "MultiLine"
  | .Add => "Add"
  | .Minus => "Minus"
  | .Mul => "Mul"
  | .Frac => "Frac"
  | .Abs => "Abs"
  | .Rel => "Rel"
  | .Implies => "Implies"

def parseNodeType (node : Name) : CoreM NodeType := do
  match node with
  | `UnknownType => return .UnknownType
  | `Text => return .Text
  | `Display => return .Display
  | `Unit => return .Unit
  | `Supscript => return .Supscript
    | `BySupscript => return .BySupscript
  | `Subscript => return .Subscript
    | `BySubscript => return .BySubscript
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

abbrev NodeInfo := String × NodeType
abbrev ExprRecFunc := Expr → NodeType → List DisplayType → List (FVarId × String) → MetaM String
abbrev ExprPassFunc := Array Expr → Expr → MetaM String
abbrev Rule := Expr → ExprRecFunc → List DisplayType → List (FVarId × String) → MetaM (Option NodeInfo)
abbrev MetaRule := Expr → ExprRecFunc → NodeType → List DisplayType → List (FVarId × String) → MetaM (Option NodeInfo)

initialize JSON_boxes : IO.Ref (Array (Name × Array Json)) ← IO.mkRef #[]
initialize Var_Usages : IO.Ref (Array (String × Array Bool)) ← IO.mkRef #[]

end Lean2TeX
