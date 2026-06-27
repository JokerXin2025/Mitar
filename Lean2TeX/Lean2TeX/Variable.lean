import Lean2TeX.Defs
import Lean2TeX.Utils

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
