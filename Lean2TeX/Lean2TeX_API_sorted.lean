-- === 外部依赖 (External Imports) ===
import Lean

-- ========================================== --
-- File: Lean2TeX/Prelude.lean
-- ========================================== --

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

abbrev NodeInfo := String × NodeType × NodeRole
abbrev ExprRecFunc := Expr → NodeType → List DisplayType → List (FVarId × String) → MetaM String
abbrev ExprPassFunc := Array Expr → Expr → MetaM String
abbrev Rule := Expr → ExprRecFunc → List DisplayType → List (FVarId × String) → MetaM (Option NodeInfo)
abbrev MetaRule := Expr → ExprRecFunc → NodeType → List DisplayType → List (FVarId × String) → MetaM (Option NodeInfo)

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
-- ========================================== --
-- File: Lean2TeX/Attributes.lean
-- ========================================== --

open Lean2TeX
open Lean

declare_syntax_cat identList
syntax "[" ident,* "]" : identList

declare_syntax_cat configItem
syntax "target_display" ":=" ident : configItem
syntax "args_display" ":=" "[" identList,* "]" : configItem
syntax "args_context_node" ":=" "[" ident,* "]" : configItem

syntax (name := Lean2TeX) "Lean2TeX" ppSpace str ppSpace ident (ppSpace "(" ppSpace configItem,* ")")? : attr

initialize Templates : MapDeclarationExtension TemplateData ← mkMapDeclarationExtension
initialize
  registerBuiltinAttribute {
    name := `Lean2TeX
    descr := "Lean2TeX Templates with Configurations"
    add := fun declName stx attrKind => do
      match stx with
      | `(attr| Lean2TeX $template:str $node:ident $[($items,*)]?) =>
        let mut config : TemplateConfig := {}
        if let some itemsArray := items then
          for item in itemsArray.getElems do
            match item with
            | `(configItem| target_display := $t:ident) =>
                let tType ← parseDisplayType t.getId
                config := { config with TargetDisplay := tType }
            | `(configItem| args_display := [$lists,*]) =>
                let dTypes ← lists.getElems.toList.mapM fun listStx => do
                  match listStx.raw with
                  | `(identList| [$ds,*]) =>
                      ds.getElems.toList.mapM (fun d => parseDisplayType d.getId)
                  | _ => throwError "Invalid inner list syntax in argsDisplay"
                config := { config with ArgsDisplay := dTypes }
            | `(configItem| args_context_node := [$ns,*]) =>
                let nTypes ← ns.getElems.toList.mapM (fun n => parseNodeType n.getId)
                config := { config with ArgsContextNode := nTypes }
            | _ => throwError "Invalid configuration item syntax"
        let data := {
          template := template.getString
          node := ← parseNodeType node.getId
          config := config
        }
        setEnv (Templates.insert (← getEnv) declName data)
      | _ => throwError "Invalid Lean2TeX attribute syntax"
  }
-- ========================================== --
-- File: Lean2TeX/Utils.lean
-- ========================================== --

namespace Lean2TeX

open Lean Meta in
/-- `∃` counterpart of `lambdaTelescope` and `forallTelescope` -/
partial def existsTelescope (expr : Expr) (expr_pass : ExprPassFunc) : MetaM String := do
  if expr.isAppOfArity' ``Exists 2 then
    return ← lambdaBoundedTelescope expr.getAppArgs'[1]! 1 fun newFvar body => do
      existsTelescope body fun restFvars finalBody =>
        expr_pass (newFvar ++ restFvars) finalBody
  else
    expr_pass #[] expr

/-- Check if the concept is a complex definition (contains `brecOn` `casesOn` `recOn`) -/
def Expr.isComplexDef (expr : Expr) : Bool :=
  Option.isSome <| expr.find? fun
  | .const n _ =>
    let s := n.toString
    s.contains "brecOn" || s.contains "casesOn" || s.contains "recOn"
  | _ => false

open Lean Elab.Tactic in
/-- Get the expression of current goal -/
def GetGoal : TacticM Expr := do
  let goal ← getMainGoal
  let goal_expr ← goal.getType
  return ← instantiateMVars goal_expr

/-- Add JSON objects `json_obj` to the JSON array -/
def addtoBox (box : Name) (json_obj : Json) : MetaM Unit := do
  JSON_boxes.modify fun arr =>
    match arr.findIdx? (fun (b, _) => b == box) with
    | some idx =>
      let (b, items) := arr[idx]!
      arr.set! idx (b, items.push json_obj)
    | none =>
      /- create the JSON array for the first time -/
      arr.push (box, #[json_obj])

/-- Automatic TeX Wrapper based on `NodeType` and `NodeRole` -/
def NodeInfo.WrappedIn (nodeInfo : NodeInfo) (parent : NodeType) : MetaM String := do
  let mut (expr, type, role) := nodeInfo
  /- Operation Priority -/
  if type == .Add && parent == .Mul then
    expr := s!"\\left({expr}\\right)"
  /- Base of Power Expression -/
  if role == .base && parent == .Supscript then
    if type == .Add || type == .Mul || type == .Supscript then
      expr := s!"\\left({expr}\\right)"
  /- Inline Equation -/
  if type != .Text && parent == .Text then
    expr := s!" ${expr}$ "
  /- Embedded Text -/
  if type == .Text && parent != .Text then
    expr := s!"\\text{"{"}{expr}{"}"}"
  return expr

end Lean2TeX
-- ========================================== --
-- File: Lean2TeX/Constant.lean
-- ========================================== --

open Lean2TeX
open Lean Meta ConstantInfo

namespace Lean2TeX

def Lean.Expr.getConstDef : MetaRule := fun expr expr_rec parent styles fvars => do
  /- Move `.Def` from the DisplayType list -/
  let styles := styles.erase .Def
  match ← getConstInfo expr.constName! with
  /- __Expression or Equations__ -/
  | defnInfo defn => do
    if Expr.isComplexDef defn.value then
      if let some eqns ← getEqnsFor? expr.constName! then
        let mut output_array := #[]
        for eqnName in eqns do
          let next ← expr_rec (← getConstInfo eqnName).type .MultiLine styles fvars
          output_array := output_array.push next
        let output := "\\\\".intercalate output_array.toList
        let output' := s!"$$\\begin{"{"}cases{"}"}{output}\\end{"{"}cases{"}"}$$"
        return (output', NodeType.Text)
      else
        return none
    else
      return (← expr_rec defn.value parent styles fvars, parent)
  /- __Theorem (or Lemma)__ -/
  | thmInfo thm => do
    return (← expr_rec thm.type parent styles fvars, parent)
  /- __Axiom__ -/
  | axiomInfo _axiom => do
    return (← expr_rec _axiom.type parent styles fvars, parent)
  /- __Inductive__ -/
  | inductInfo _ /- induct -/ =>
    return none
    /-
    let texType ← Expr2TeX induct.type
    queueLatexInfo box.getId s!"{nameStr}_type" texType
    let mut idx := 1
    for ctorName in induct.ctors do
        let ctorDecl ← getConstInfo ctorName
        let ctorTex ← Expr2TeX ctorDecl.type
        let outName := s!"{nameStr}_ctor{idx}"
        queueLatexInfo box.getId outName ctorTex
        idx := idx + 1
    -/
  /- __Constructor__ -/
  | ctorInfo _ =>
    return none
  /- __Recursor / Eliminator__ -/
  | recInfo _ => do
    return none
  /- __Opaque__ -/
  | opaqueInfo _ => do
    return none
  /- __Quotient Info__ -/
  | quotInfo _ => do
    return none

end Lean2TeX
-- ========================================== --
-- File: Lean2TeX/Variable.lean
-- ========================================== --

open Lean2TeX
open Lean Meta

namespace Lean2TeX

def resetVarAllocator : IO Unit := do
  Var_Usages.set #[]

def allocateVar (varType : String) : MetaM (String × Nat) := do
  let usageArray ← Var_Usages.get
  let mut usage := #[]
  let mut foundMapIdx : Option Nat := none
  for i in [0:usageArray.size] do
    if usageArray[i]!.1 == varType then
      usage := usageArray[i]!.2
      foundMapIdx := some i; break
  let mut foundIdx : Option Nat := none
  for i in [0:usage.size] do
    if usage[i]! == false then
      foundIdx := some i; break
  let idx := foundIdx.getD usage.size
  let newUsage := if foundIdx.isSome then usage.set! idx true else usage.push true
  if let some i := foundMapIdx then
    Var_Usages.set (usageArray.set! i (varType, newUsage))
  else
    Var_Usages.set (usageArray.push (varType, newUsage))
  return (s!"{varType}{idx + 1}", idx)

def releaseVar (bfvarInfo : String × Nat) : MetaM Unit := do
  let usageArray ← Var_Usages.get
  for i in [0:usageArray.size] do
    if usageArray[i]!.1 == bfvarInfo.1 then
      let usage := usageArray[i]!.2
      if bfvarInfo.2 < usage.size then
        Var_Usages.set (usageArray.set! i (bfvarInfo.1, usage.set! bfvarInfo.2 false))
      break

def parseBVar (part : String) : Option (Nat × String × String) := Id.run do
  let mut j := 0
  let charsArray := part.toList.toArray
  /- Extract the index from `charsArray` -/
  let mut indexStr := ""
  while j < charsArray.size && charsArray[j]!.isDigit do
    indexStr := indexStr.push charsArray[j]!
    j := j + 1
  if indexStr == "" || j >= charsArray.size || charsArray[j]! != '(' then
    return none
  j := j + 1
  /- Extract the type string from `charsArray` -/
  let mut typeStr := ""
  while j < charsArray.size && charsArray[j]! != ')' do
    typeStr := typeStr.push charsArray[j]!
    j := j + 1
  if j >= charsArray.size || charsArray[j]! != ')' then
    return none
  j := j + 1
  /- return the index, type string, and the remaining string -/
  return some (indexStr.toNat!, typeStr, String.ofList (charsArray.toList.drop j))

def processPlaceholders (s : String) : MetaM (String × Array (Option (String × Nat))) := do
  let parts := (s.splitOn "#").toArray
  if parts.size <= 1 then
    return (s, #[])
  let mut result := parts[0]!
  -- 核心映射数组：索引 n 存放着 #n 对应的 (类型, 全局变量索引)
  let mut allocatedArray : Array (Option (String × Nat)) := #[]
  for i in [1:parts.size] do
    let part := parts[i]!
    if result.endsWith "\\" then
      result := result ++ "#" ++ part
    else
      match parseBVar part with
      | some (n, typeStr, restStr) =>
          -- 【核心逻辑 1】：按需扩容数组。如果 n 超出了当前数组边界，用 none 填补空缺
          if n >= allocatedArray.size then
            let mut temp := allocatedArray
            while temp.size <= n do
              temp := temp.push none
            allocatedArray := temp
          -- 【核心逻辑 2】：直接通过索引 n 瞬间判断是否分配过
          match allocatedArray[n]! with
          | some (existingType, existingIdx) =>
              -- 严谨检查：如果发现同一个 #n 对应了不同类型，抛出错误
              if existingType != typeStr then
                throwError s!"占位符冲突：#n 为 {n} 时，前面使用了类型 {existingType}，现在却使用类型 {typeStr}"
              -- 直接拼接之前生成的变量名（如 "Real1"）
              let name := s!"{existingType}{existingIdx + 1}"
              result := result ++ name ++ restStr
          | none =>
              -- 还没分配过，向全局申请新变量
              let (name, idx) ← allocateVar typeStr
              -- 记录入数组的第 n 个位置
              allocatedArray := allocatedArray.set! n (some (typeStr, idx))
              result := result ++ name ++ restStr
      | none =>
          result := result ++ "#" ++ part
  return (result, allocatedArray)
-- ========================================== --
-- File: Lean2TeX/Rules/Logic.lean
-- ========================================== --

open Lean2TeX
open Lean.Meta (forallTelescope)
open Lean2TeX.Meta (existsTelescope)

def Rule_False_Word : Rule := fun expr _ _ _ => do
  if expr.isConstOf ``False then
    return (s!"矛盾", NodeType.Text)
  return none

def Rule_And_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Int 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text styles fvars
    let B ← expr_rec args[1]! .Text styles fvars
    return (s!"{A}且{B}", NodeType.Text)
  return none

def Rule_Or_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity `Or 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text styles fvars
    let B ← expr_rec args[1]! .Text styles fvars
    return (s!"{A}或{B}", NodeType.Text)
  return none

def Rule_Iff_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity `Iff 2 then
    let args := expr.getAppArgs
    let A ← expr_rec args[0]! .Text styles fvars
    let B ← expr_rec args[1]! .Text styles fvars
    return (s!"{A}当且仅当{B}", NodeType.Text)
  return none

def Rule_Not_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity `Not 1 then
    let arg := expr.getAppArgs[0]!
    let A ← expr_rec arg .Text styles fvars
    if arg.isAppOfArity ``Exists 2 then
      return (s!"不{A}", NodeType.Text)
    else
      return (s!"命题{A}不成立", NodeType.Text)
  return none

def Rule_Implies_Symbol : Rule := fun expr expr_rec styles fvars => do
  match expr with
  | .forallE _ binder body _ => do
      if expr.isArrow then
        let XXX ← expr_rec binder .Implies styles fvars
        let YYY ← expr_rec body .Implies styles fvars
        return (s!"{XXX}\\implies {YYY}", NodeType.Implies)
      else
        return none
  | _ => return none

def Rule_Forall_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isForall then
    if !expr.isArrow then
      let res ← forallTelescope expr fun _fvars body => do
        let XXX ← expr_rec body .Text styles fvars
        match _fvars.size with
        | 1 =>
          let x ← expr_rec _fvars[0]! .Rel styles fvars
          let A ← expr_rec (← inferType _fvars[0]!) .Rel styles fvars
          return s!"{XXX}对一切 ${x}\\in {A}$ 成立"
        | 2 =>
          let typeExpr1 := ← inferType _fvars[0]!
          let typeExpr2 := ← inferType _fvars[1]!
          match ← isProp typeExpr1, ← isProp typeExpr2 with
          | true, true =>
            let A ← expr_rec typeExpr1 .Text styles fvars
            let B ← expr_rec typeExpr2 .Text styles fvars
            return s!"若{A}且{B}, 则{XXX}"
          | true, false => return ""
          | false, true =>
            let x ← expr_rec _fvars[0]! .Rel styles fvars
            let A ← expr_rec typeExpr1 .Rel styles fvars
            let B ← expr_rec typeExpr2 .Text styles fvars
            return s!"对任意满足{B}的 ${x}\\in {A}$ 有{XXX}"
          | false, false =>
            let x ← expr_rec _fvars[0]! .Rel styles fvars
            let y ← expr_rec _fvars[1]! .Rel styles fvars
            let A ← expr_rec typeExpr1 .Rel styles fvars
            let B ← expr_rec typeExpr2 .Rel styles fvars
            return s!"{XXX}对一切 ${x}\\in {A}$ 和 ${y}\\in {B}$ 成立"
        | _ =>
          let mut xAyB_array := #[]
          for fvar in _fvars do
            let x ← expr_rec fvar .Rel styles fvars
            let A ← expr_rec (← inferType fvar) .Rel styles fvars
            xAyB_array := xAyB_array.push s!"{x}\\in {A}"
          let xAyB := "\\,,\\,".intercalate xAyB_array.toList
          return s!"对任意 ${xAyB}$ 有: {XXX}"
      return (res, NodeType.Text)
    else
      return none
  else
    return none

def Rule_Exists_Word : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Exists 2 then
    let res ← existsTelescope expr fun _fvars safeBody => do
      let mut varList := #[]
      for fvar in _fvars do
        let x ← expr_rec fvar .Rel styles fvars
        let A ← expr_rec (← inferType fvar) .Rel styles fvars
        varList := varList.push s!"{x}\\in{A}"
      let xAyB := "\\,,\\,".intercalate varList.toList
      let XXX ← expr_rec safeBody .Text styles fvars
      return s!"存在 ${xAyB}$ 使得{XXX}"
    return (res, NodeType.Text)
  return none
-- ========================================== --
-- File: Lean2TeX/Rules/Operations.lean
-- ========================================== --

open Lean2TeX

def Rule_Succ : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Nat.succ 1 then
    let args := expr.getAppArgs
    let n ← expr_rec args[0]! .Add styles fvars
    return (s!"{n}+1", NodeType.Add)
  return none

def Rule_Add : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HAdd.hAdd 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Add styles fvars
    let B ← expr_rec args[5]! .Add styles fvars
    return (s!"{A}+{B}", NodeType.Add)
  return none

def Rule_Sub : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HSub.hSub 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Add styles fvars
    let B ← expr_rec args[5]! .Add styles fvars
    return (s!"{A}-{B}", NodeType.Add)
  return none

def Rule_Mul : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HMul.hMul 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Mul styles fvars
    let B ← expr_rec args[5]! .Mul styles fvars
    return (s!"{A}\\cdot {B}", NodeType.Mul)
  return none

def Rule_Div : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HDiv.hDiv 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .Frac styles fvars
    let B ← expr_rec args[5]! .Frac styles fvars
    return (s!"\\frac{"{"}{A}{"}"}{"{"}{B}{"}"}", NodeType.Frac)
  return none

def Rule_Pow : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``HPow.hPow 6 then
    let args := expr.getAppArgs
    let A ← expr_rec args[4]! .BySupscript styles fvars
    let B ← expr_rec args[5]! .Supscript styles fvars
    return (s!"{A}^{"{"}{B}{"}"}", NodeType.Supscript)
  return none

def Rule_Neg : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Neg.neg 3 then
    let args := expr.getAppArgs
    let X ← expr_rec args[2]! .Minus styles fvars
    return (s!"-{X}", NodeType.Minus)
  return none

def Rule_Inv : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Inv.inv 3 then
    let args := expr.getAppArgs
    let X ← expr_rec args[2]! .BySupscript styles fvars
    return (s!"{X}^{"{"}-1{"}"}", NodeType.Supscript)
  return none

def Rule_Abs : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity `abs 4 then
    let args := expr.getAppArgs
    let X ← expr_rec args[3]! .Abs styles fvars
    return (s!"\\left|{X}\\right|", NodeType.Abs)
  return none
-- ========================================== --
-- File: Lean2TeX/Rules/Relations.lean
-- ========================================== --

open Lean2TeX

def Rule_Eq : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Eq 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! .Rel styles fvars
    let B ← expr_rec args[2]! .Rel styles fvars
    return (s!"{A}={B}", NodeType.Rel)
  return none

def Rule_NotEq : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``Ne 3 then
    let args := expr.getAppArgs
    let A ← expr_rec args[1]! .Rel styles fvars
    let B ← expr_rec args[2]! .Rel styles fvars
    return (s!"{A}\\ne {B}", NodeType.Rel)
  return none

def Rule_Less : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``LT.lt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}<{B}", NodeType.Rel)
  return none

def Rule_LessEqual : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``LE.le 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}\\leqslant {B}", NodeType.Rel)
  return none

def Rule_Greater : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``GT.gt 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}>{B}", NodeType.Rel)
  return none

def Rule_GreaterEqual : Rule := fun expr expr_rec styles fvars => do
  if expr.isAppOfArity ``GE.ge 4 then
    let args := expr.getAppArgs
    let A ← expr_rec args[2]! .Rel styles fvars
    let B ← expr_rec args[3]! .Rel styles fvars
    return (s!"{A}\\geqslant {B}", NodeType.Rel)
  return none
-- ========================================== --
-- File: Lean2TeX/Rules/NumberSystem.lean
-- ========================================== --

open Lean2TeX

def Rule_Mathbb_Nat : Rule := fun expr _ _ _ => do
  if expr.isConstOf ``Nat then
    return (s!"\\mathbb{"{"}N{"}"}", NodeType.Unit)
  return none

def Rule_Mathbf_Nat : Rule := fun expr _ _ _ => do
  if expr.isConstOf ``Nat then
    return (s!"\\mathbf{"{"}N{"}"}", NodeType.Unit)
  return none

def Rule_Mathbb_Real : Rule := fun expr _ _ _ => do
  if expr.isConstOf `Real then
    return (s!"\\mathbb{"{"}R{"}"}", NodeType.Unit)
  return none

def Rule_Mathbf_Real : Rule := fun expr _ _ _ => do
  if expr.isConstOf `Real then
    return (s!"\\mathbf{"{"}R{"}"}", NodeType.Unit)
  return none
-- ========================================== --
-- File: Lean2TeX/Rules/Calculus.lean
-- ========================================== --

open Lean2TeX

def Rule_NumSeq : Rule := fun expr expr_rec styles fvars => do
  if expr.isApp then
    if (← inferType expr.appArg!).isConstOf ``Nat then
      let a ← expr_rec expr.appFn! .BySubscript ([.Plain] ++ styles) fvars
      let n ← expr_rec expr.appArg! .Subscript styles fvars
      return (s!"{a}_{"{"}{n}{"}"}", NodeType.Subscript)
  return none

def Rule_Func : Rule := fun expr expr_rec styles fvars => do
  if expr.isApp then
    if (← inferType expr.appArg!).isConstOf `Real then
      let f ← expr_rec expr.appFn! .BracApp ([.Plain] ++ styles) fvars
      let x ← expr_rec expr.appArg! .BracApp styles fvars
      return (s!"{f}({x})", NodeType.BracApp)
  return none
-- ========================================== --
-- File: Lean2TeX/Rules.lean
-- ========================================== --

open Lean2TeX
open Lean (getEnv)
open Lean.Meta (lambdaTelescope)

def MetaRule_Lambda : MetaRule := fun expr expr_rec parent styles fvars => do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _ body =>
      expr_rec body parent styles fvars
    return (res, parent)
  return none

def MetaRule_Lambda' : Expr → ExprRecFunc → NodeType → List DisplayType → List (FVarId × String) → Array String → MetaM (Option String) := fun expr expr_rec parent styles fvars fvar_strings => do
  if expr.isLambda then
    let res ← lambdaTelescope expr fun _fvars body =>
      expr_rec body parent styles (fvars.toArray ++ (_fvars.map (fun expr => expr.fvarId!)).zip fvar_strings).toList
    return res
  return none  -- change to `""` ?

def MetaRule_OfNat : MetaRule := fun expr expr_rec parent styles fvars => do
  if expr.isAppOfArity' ``OfNat.ofNat 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[1]! parent styles fvars, parent)
  return none

def MetaRule_Cast : MetaRule := fun expr expr_rec parent styles fvars => do
  if expr.isAppOfArity' ``Nat.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent styles fvars, parent)
  else if expr.isAppOfArity' ``Int.cast 3 then
    let args := expr.getAppArgs'
    return (← expr_rec args[2]! parent styles fvars, parent)
  return none

def Rule_Generic : Rule := fun expr expr_rec styles fvars => do
  let fn := expr.getAppFn
  match fn with
  | .const declName _ =>
    let env ← getEnv
    if let some templateData := Templates.find? env declName then
      let args := expr.getAppArgs
      let targetDisplay := templateData.config.TargetDisplay
      let argsDisplay := templateData.config.ArgsDisplay.toArray
      let argsContextNode := templateData.config.ArgsContextNode.toArray
      let mut evaledArgs := #[]
      let mut (res, fvar_list) ← processPlaceholders templateData.template
      let mut n := 0
      for arg in args do
        let argDisplay := (argsDisplay[n]?.getD []) ++ styles
        let argContextNode := argsContextNode[n]?.getD templateData.node
        if let some fvar_info? := fvar_list[n+1]? then
          if let some (type, index) := fvar_info? then
            if let some res' ← MetaRule_Lambda' arg.consumeMData expr_rec argContextNode argDisplay fvars #[s!"{type}{index+1}"] then
              evaledArgs := evaledArgs.push res'
            else
              let arg ← expr_rec arg argContextNode argDisplay fvars
              evaledArgs := evaledArgs.push arg
            releaseVar (type, index)
        else
          let arg ← expr_rec arg argContextNode argDisplay fvars
          evaledArgs := evaledArgs.push arg
        n := n + 1
      for i in [0:args.size] do
        res := res.replace s!"@{i+1}" evaledArgs[i]!
      return some (res, templateData.node)
    return none
  | _ => return none

def PresetMetaRules : List MetaRule := [
  (MetaRule_Lambda),
  (MetaRule_OfNat),
  (MetaRule_Cast)
]

def PresetRules : List (Rule × DisplayType) := [
  (Rule_Generic, .Basic),
  (Rule_False_Word, .Basic), (Rule_False_Word, .Word),
  (Rule_And_Word, .Basic), (Rule_And_Word, .Word),
  (Rule_Or_Word, .Basic), (Rule_Or_Word, .Word),
  (Rule_Iff_Word, .Basic), (Rule_Iff_Word, .Word),
  (Rule_Not_Word, .Basic), (Rule_Not_Word, .Word),
  (Rule_Implies_Symbol, .Basic), (Rule_Implies_Symbol, .Symbol),
  (Rule_Forall_Word, .Basic), (Rule_Forall_Word, .Word),
  (Rule_Exists_Word, .Basic), (Rule_Exists_Word, .Word),
  (Rule_Succ, .Basic),
  (Rule_Add, .Basic),
  (Rule_Sub, .Basic),
  (Rule_Mul, .Basic),
  (Rule_Div, .Basic),
  (Rule_Pow, .Basic),
  (Rule_Neg, .Basic),
  (Rule_Inv, .Basic),
  (Rule_Abs, .Basic),
  (Rule_Eq, .Basic),
  (Rule_NotEq, .Basic),
  (Rule_Less, .Basic),
  (Rule_LessEqual, .Basic),
  (Rule_Greater, .Basic),
  (Rule_GreaterEqual, .Basic),
  (Rule_Mathbb_Nat, .Basic), (Rule_Mathbb_Nat, .Mathbb),
  (Rule_Mathbb_Real, .Basic), (Rule_Mathbb_Real, .Mathbb),
  (Rule_Mathbf_Nat, .Mathbf),
  (Rule_Mathbf_Real, .Mathbf),
  (Rule_NumSeq, .Basic),
  (Rule_Func, .Basic)
]
-- ========================================== --
-- File: Lean2TeX/Core.lean
-- ========================================== --

open Lean2TeX NodeInfo

namespace Lean2TeX

partial def Expr2TeX (expr : Expr) (parent : NodeType) (styles : List DisplayType) (fvars : List (FVarId × String)) : MetaM String := do
  /- Match with preseted metarules of same `DisplayType` -/
  for metarule in PresetMetaRules do
    if let some res ← metarule expr.consumeMData Expr2TeX parent styles fvars then
      return ← res.WrappedIn parent
  /- Match with preseted rules of same `DisplayType` -/
  for (rule, rule_style) in PresetRules do
    if styles.contains rule_style then
      if let some res ← rule expr.consumeMData Expr2TeX styles fvars then
        return ← res.WrappedIn parent
  /- Match with preseted rules of `.Basic` by default -/
  for (rule, rule_style) in PresetRules do
    if rule_style == .Basic then
      if let some res ← rule expr.consumeMData Expr2TeX styles fvars then
        return ← res.WrappedIn parent
  /- Error Handling & Core Procession -/
  match expr with
  | .sort _ => return "[sort]"
  | .bvar _ => return "[bvar]"
  | .mvar _ => return "[mvar]"
  | .proj _ _ _ => return "[proj]"
  | .lam _ _ _ _ => return "[lam]"
  /- This case will never be executed due to `MetaRule_Lambda` -/
  | .forallE _ _ _ _ => return "[forallE]"
  /- This case will never be executed due to `Rule_Implies` and `Rule_Forall` -/
  | .letE _ _ _ _ _ => return "[letE]"
  | .lit (.natVal n) => return ← WrappedIn (s!"{n}", .Unit) parent
  | .lit (.strVal s) => return ← WrappedIn (s, .Text) parent
  | .app fn arg => do
    let f ← Expr2TeX fn .BracApp styles fvars
    let x ← Expr2TeX arg .BracApp styles fvars
    return ← WrappedIn (s!"{f}[{x}]", .BracApp) parent
  | .const const _ =>
    if styles.contains .Def then
      if let some res ← expr.getConstDef Expr2TeX parent styles fvars then
        return ← res.WrappedIn parent
      else
        return ""
    else
      return ← WrappedIn (const.toString, .Unit) parent  -- !
  | .fvar fvar => do
    let decl ← fvar.getDecl
    match decl.value? with
    | some val => return ← Expr2TeX val parent styles fvars
    | none =>
      if ← isProp decl.type then
        return ← Expr2TeX decl.type parent styles fvars
      else
        if let some fvar_name! := fvars.lookup fvar then
          return ← WrappedIn (fvar_name!, .Unit) parent
        else
          return ← WrappedIn (decl.userName.toString, .Unit) parent
  | .mdata _ expr' => Expr2TeX expr' parent styles fvars

end Lean2TeX
-- ========================================== --
-- File: Lean2TeX/Commands.lean
-- ========================================== --

open Lean2TeX
open Lean Elab Command Term

/-- View constant's definition -/
elab "#Lean2TeX_const" const:ident : command => liftTermElabM do
  let expr ← instantiateMVars (← elabTerm const none)
  let output ← Expr2TeX expr .Text [.Def] []
  logInfo m! "[Lean2TeX] {const} :\n{output}"

/-- Export JSON box into a JSON file (as JSON array) -/
elab "#Lean2TeX" box:ident file:str : command => do
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
-- ========================================== --
-- File: Lean2TeX/Tactics.lean
-- ========================================== --

open Lean2TeX
open Lean Elab Tactic

/-- Add information to a JSON array -/
syntax "Lean2TeX" ident "<-"
    (str)? ("_goal_")? (colGt ident ("(" str ")")?)*
    (colGt "*" ident ("(" str ")")?)* (colGt "&" ident ("(" str ")")?)* : tactic
/-- Merge JSON values into a new JSON array -/
syntax "Lean2TeX" "vals" ident "<-"
    (colGt "*" ident)* (colGt "&" ident)* : tactic

elab_rules : tactic
| `(tactic| Lean2TeX $box:ident <-
    $[$name:str]? $[$args:ident$[($arg_keys:str)]?]*
    $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  addObj box name args arg_keys ptrs ptr_keys arrs arr_keys false
| `(tactic| Lean2TeX $box:ident <-
    $[$name:str]? _goal_ $[$args:ident$[($arg_keys:str)]?]*
    $[* $ptrs:ident$[($ptr_keys:str)]?]* $[& $arrs:ident$[($arr_keys:str)]?]*) =>
  addObj box name args arg_keys ptrs ptr_keys arrs arr_keys true
| `(tactic| Lean2TeX vals $box:ident <-
    $[* $ptrs:ident]* $[& $arrs:ident]*) =>
  addVals box ptrs arrs
-- ========================================== --
-- File: Lean2TeX.lean
-- ========================================== --
