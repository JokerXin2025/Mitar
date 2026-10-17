# Lean2TeX 变量管理系统

## 概述

Lean2TeX 不直接使用 Lean 中的变量名, 而是运行一套 **全局变量分配器** , 为每个变量生成人类可读的符号名 (如 $x, y, z, n, m, i$ ) . 这套系统保证:

1. **类型决定的命名池** : 实数用 $x, y, z, a$ , 自然数用 $n, m, i, j$
2. **全局唯一** : 同名池（如 ℕ 和 ℤ 都含 `n`）不会冲突——先分配的类型占用该名，后分配的类型自动跳过
3. **作用域感知** : lambda / forall 绑定的变量在作用域结束时释放, 可供后续复用
4. **外部可配置** : 通过 `Variables.toml` 配置所有类型和名称池，无需修改代码
5. **一致性** : 同一个自由变量在多个渲染位置始终获得同一个符号名（FVarNameCache）

---

## 架构分层

```
┌─────────────────────────────────────────────────┐
│  Variables.toml                              │
│  外部配置文件：[[type]] name / default / var_names  │
├─────────────────────────────────────────────────┤
│  VariableToml.lean                                │
│  TOML 解析 → TypeConfig / VarConfig 数据结构       │
├─────────────────────────────────────────────────┤
│  Prelude.lean                                     │
│  Var_AllocatedNames（全局唯一名称集）                │
│  FVarNameCache（FVarId → name 缓存）               │
├─────────────────────────────────────────────────┤
│  Variable.lean                                    │
│  allocateVar / releaseVar / typeExprToTypeStr      │
│  哨兵占位符 / processPlaceholders                   │
├─────────────────────────────────────────────────┤
│  Rules.lean / Rules/Init.lean                      │
│  Rule_Generic / processLambda / Rule_Forall_Word   │
│  负责：触发变量分配、管理 fvars 列表、释放          │
├─────────────────────────────────────────────────┤
│  Core.lean                                        │
│  Expr2TeX → .fvar case（FVarNameCache → allocateVar）│
└─────────────────────────────────────────────────┘
```

---

## 核心数据

### 全局状态（`Prelude.lean`）

```lean
initialize Var_AllocatedNames : IO.Ref (List String)
  -- 全局已分配名称集合（跨类型唯一性保证）

initialize FVarNameCache : IO.Ref (List (FVarId × String))
  -- FVarId → 已分配变量名 的缓存
  -- 确保同一 FVar 在 forall 头部和 body 等多处渲染时得到同一名字
```

### 核心函数签名

```lean
-- 分配：全局唯一名称
allocateVar (typeStr : String) : MetaM String

-- 释放：将名称标记为空闲
releaseVar (name : String) : MetaM Unit

-- 重置：清空所有使用记录（每次新定理开始时调用）
resetVarAllocator : IO Unit

-- 类型表达式 → 短类型字符串
typeExprToTypeStr (type : Expr) (exprRec : ...) : MetaM String
```

---

## TOML 配置格式

```toml
[[type]]
name = "Real"          # Lean 常量名
default = "ℝ"          # 短名，池耗尽后用作 ℝ_{n} 前缀
var_names = ["x", "y", "z", "a", "b", "c", "u", "v", "w"]  # 名称池
```

- **`name`**：`typeExprToTypeStr` 用 `.const` 名称匹配此项
- **`default`**：池耗尽时用作回退前缀（如 `default = "ℝ"` → `ℝ_{1}`, `ℝ_{2}`）
- **`var_names`**：按顺序取用的人类可读名称列表

要添加新类型（如 `Complex`），只需增加一个 `[[type]]` 条目。若 TOML 文件缺失，系统回退到内置默认配置。

---

## 变量命名池

每种类型有预设的名字列表。分配时按顺序取用（跨类型检查全局唯一）；池耗尽后回退到 `{default}_{n}` 格式。

| 类型 `name` | `default` | 池内名字 | 回退格式 |
|-----------|---------|---------|---------|
| `Real` | `ℝ` | `x, y, z, a, b, c, u, v, w` | `ℝ_{10}`, `ℝ_{11}` |
| `Nat` | `ℕ` | `n, m, i, j, k, p, q` | `ℕ_{8}`, `ℕ_{9}` |
| `Int` | `ℤ` | `n, m, i, j, k, p, q` | `ℤ_{8}`, `ℤ_{9}` |
| `Rat` | `ℚ` | `r, s, t` | `ℚ_{4}`, `ℚ_{5}` |

### 全局唯一性

ℕ 和 ℤ 池中都有 `n`。在同一个定理中：
- 若先分配 ℕ 变量 → 获得 `n`，`Var_AllocatedNames` 记录 `n` 已占用
- 后分配 ℤ 变量 → 检查 `n` 已被占用 → 跳到下一个池名 `m`
- 若 ℤ 池中的 `n, m, i, j, k, p, q` 全被占用 → 使用回退 `ℤ_{1}`

这保证了 KaTeX 输出中不会出现两个无法区分的 `n`。

---

## 两条变量生成路径

### FVar 自由变量 → Core.lean 的 `.fvar` 分支

**适用场景**：定理的顶层参数、forall/exists 绑定变量（通过 telescope 转为 FVar 后）

**查找优先级**（三级 Fallback）：

```
.fvar fvar → 
  ① fvars 列表（lambda 绑定的名字）       ── 命中 → 使用
  ② FVarNameCache（全局缓存）              ── 命中 → 复用
  ③ allocateVar(typeExprToTypeStr(type))  ── 首次 → 分配 + 写入缓存
```

### BVar 绑定变量 → 模板占位符 `#n`

**适用场景**：Lambda 函数体内的绑定变量，由模板属性中的 `#1` `#2` 引用

**流程**：

```
模板 "@1 在 #1(ℝ) 处取值"
  ↓ processPlaceholders  在 Variable.lean
  ↓ #1(ℝ) → allocateVar("ℝ") → x
模板变为 "@1 在 x 处取值"

  ↓ Rule_Generic 在 Rules.lean
  ↓ 处理 arg @1（是 lambda 表达式）
  ↓ processLambda_withFVars
  ↓ lambdaTelescope → 把 BVar 转为 FVar
  ↓ 将 FVar 与 "x" 绑定 → 写入 fvars 列表
  ↓ 递归渲染 lambda body

结果：lambda body 中所有该变量的出现都用 "x"
```

---

## `typeExprToTypeStr` 类型映射

```
Expr (type)
  ↓ whnf
  ├─ .const name _  → 查 TOML name 字段 → 返回 default
  │                   未找到 → 返回 name.toString（如 "MyColor"）
  ├─ .sort _        → 查 TOML name="Sort" → 返回 default（默认 "Type"）
  └─ _ (其他)       → 调用 Expr2TeX 渲染类型
                      → 返回 \LeanToTeXvar{<typeTeX>}
                      → allocateVar 处理为 \LeanToTeXvar{<typeTeX>}{n}
```

`\LeanToTeXvar` 是一个 LaTeX 宏，交给下游 Mitar/Python 展开。例如 `Fin 5`（`.app` 类型，不是 `.const`）→ `\LeanToTeXvar{Fin_{5}}{1}`。

---

## 防止同名混乱的机制

### 1. FVarNameCache

同一个 FVarId 只会被分配**一次**名字。后续在任何地方遇到同一 FVarId，直接从缓存取。

### 2. 作用域释放

| 变量来源 | 分配位置 | 释放位置 |
|---------|---------|---------|
| 定理顶层参数 (FVar) | Core.lean `.fvar` ③ | **不释放**（跨整个定理） |
| Lambda 绑定变量 (显式 `#1(ℝ)`) | processPlaceholders | Rule_Generic 处理完 arg 后 |
| Lambda 绑定变量 (裸 `#1` 延迟) | processLambda_withFVars | 同上函数内 |
| Forall 绑定变量 | preAllocateFVars | Rule_Forall_Word 末尾 |
| Exists 绑定变量 | preAllocateFVars | Rule_Exists_Word 末尾 |

### 3. resetVarAllocator

每次新定理开始时调用（`Commands.lean` 的 `runLean2TeX`），清空 `Var_AllocatedNames` 和 `FVarNameCache`。

---

## 文件清单

| 文件 | 职责 |
|------|------|
| `Variables.toml` | 外部配置文件：`[[type]]` 格式 |
| `VariableToml.lean` | TOML 解析：`TypeConfig` / `VarConfig` / `loadVarConfig` |
| `Prelude.lean` | `Var_AllocatedNames`, `FVarNameCache` 全局状态 |
| `Variable.lean` | `allocateVar`, `releaseVar`, `typeExprToTypeStr`, 哨兵占位符, `processPlaceholders` |
| `Core.lean` | `Expr2TeX`（主递归渲染）, `.fvar` case 三级 fallback |
| `Rules.lean` | `Rule_Generic`（模板属性匹配 + 替换）, `processLambda_withFVars`, `processLambda` |
| `Rules/Init.lean` | `preAllocateFVars`, `extendFVars`, `Rule_Forall_Word`, `Rule_Exists_Word` |
| `Commands.lean` | `resetVarAllocator` 调用（每个定理开始时） |
| `Demo/Variable-System.lean` | 12 个变量系统测试用例 |
