import Lean
import Mathlib.Tactic
import «Calculus@Mitar».Limit.Expr
import «Calculus@Mitar».Limit.Rules
import «Calculus@Mitar».Limit.Infinitesimal.Equivalent

open Lean
open Elab Tactic
open Meta (lambdaTelescope ppExpr)

def parseStringToTerm (s : String) : CoreM Term := do
  let env ← getEnv
  match Parser.runParserCategory env `term s "<python_oracle>" with
  | Except.ok stx => return ⟨stx⟩
  | Except.error err => throwError "无法解析 Python 返回的表达式: {err}"


lemma Limit_Div?_None (p q : ℝ → ℝ) (x₀ : ℝ) (m : ℕ) (hm : m > 0)
    (hp : IsContinuous p x₀) (hq : IsContinuous q x₀)
    (hp_neq : p x₀ ≠ 0) (hq_neq : q x₀ ≠ 0) :
    lim (fun x ↦ p x / (q x * (x - x₀)^m)) x₀ = none := sorry


/--
  ### Tactic `limit_rational` solves limits of rational functions
  __Usage__ `limit_rational`
-/
elab "limit_rational" : tactic => do
  let goal ← getMainTarget
  -- 2. 解剖等式
  let some (_, lhs, _) := goal.eq?
  | throwError "Tactic `limit_rational` failed: The current goal is not an equation."
  -- 3. 确认左侧是 lim 调用，并提取参数
  if lhs.getAppFn.constName? != some ``FuncLimitExpr then
    throwError "等号左侧必须是 lim 求极限函数"
  let args := lhs.getAppArgs
  let f := args[args.size - 2]!
  let x0 := args[args.size - 1]!
  -- 4. 【修复点】使用纯函数式的闭包返回值，直接提取出分子分母元组！
  let (numStr, denStr) ← lambdaTelescope f fun xs body => do
    let divFn := body.getAppFn
    if divFn.constName? != some ``HDiv.hDiv && divFn.constName? != some ``Div.div then
      throwError "被求极限的函数主体不是一个除法 (分数) 表达式"
    return (← toString <$> ppExpr body.appFn!.appArg!, ← toString <$> ppExpr body.appArg!)
  -- 将趋近点转换为字符串
  let x0Str ← toString <$> ppExpr x0
  let out ← IO.Process.output {
    cmd := "/Library/Frameworks/Python.framework/Versions/3.12/bin/python3"
    args := #["limit_oracle.py", numStr, denStr, x0Str]
  }
  if out.exitCode != 0 then
    throwError "SymPy 脚本执行失败: {out.stderr}"
  let res := out.stdout.trimAscii.toString
  let pStr := (res.splitOn "\"p\": \"")[1]!.splitOn "\"" |>.head!
  let qStr := (res.splitOn "\"q\": \"")[1]!.splitOn "\"" |>.head!
  let kStr := (res.splitOn "\"k\": ")[1]!.splitOn "," |>.head!
  let mStr := (res.splitOn "\"m\": ")[1]!.splitOn "}" |>.head!
  let p ← parseStringToTerm s!"fun x : ℝ => {pStr}"
  let q ← parseStringToTerm s!"fun x : ℝ => {qStr}"
  let k ← parseStringToTerm kStr
  let m ← parseStringToTerm mStr
  if res.contains "\"is_divergent\": true" then
    evalTactic (← `(tactic| {
      apply Eq.trans (FuncLimitExpr.Congr /- (fun x ↦ $p x / ($q x * (x - _) ^ $m)) -/ (sorry))
      apply Limit_Div?_None _ _ _ _ (sorry)
      · exact Check_Continuous _ _
      · exact Check_Continuous _ _
      · exact sorry
      · exact sorry
    }))
  else
    evalTactic (← `(tactic| {
      apply Eq.trans (FuncLimitExpr.Congr /- (fun x ↦ $p x / $q x) -/ (sorry))
      rw [Continuous_Div]
      · norm_num
      · exact Check_Continuous _ _
      · exact Check_Continuous _ _
      · exact sorry
    }))

/- # Usage Examples of `limit_rational` -/

/-

--  Example 1 : $\lim_{x\to 1}\frac{x^2-1}{x-1} = 2$
example : lim (fun x ↦ (x^2 - 1) / (x - 1)) 1 = the 2 := by
  limit_rational

--  Example 2 : $\lim_{x\to 2}\frac{x^3-8}{x^2-4} = 3$
example : lim (fun x ↦ (x^3 - 8) / (x^2 - 4)) 2 = the 3 := by
  limit_rational

--  Example 3 : 极限 $\lim_{x\to 0}\frac{x+1}{x^2}$ 不存在
example : lim (fun x ↦ (x + 1) / x^2) 0 = none := by
  limit_rational

-/
