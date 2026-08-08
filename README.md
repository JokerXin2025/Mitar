# Lean2TeX + Mitar 使用指南

__*未完稿 —— 更新日期 20260804*__

__*本项目尚处开发阶段 本指南仅供预览*__
*联系方式 jokerxin@126.com*

**Lean2TeX** 是一个 Lean 4 库, 能将数学证明按特定规则自动导出为 JSON 文件

**Mitar** 是一个基于 Lean2TeX 的 Python 脚本, 用于进一步生成交互式 HTML 页面

---

## 快速开始

### 安装

```bash
git clone https://github.com/JokerXin2025/Mitar.git
cd Mitar
make install
```

确保已安装 Lean 4 及 elan 工具链

### 一分钟上手

1. 在需要导出的 Lean 证明前添加 `#Lean2TeX`

```lean
import Mathlib.Data.Real.Basic
import Lean2TeX

#load_tactics mathlib                     -- load Mathlib tactic rules

#Lean2TeX theorem my_theorem (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [ih]
```

2. 在 Lean 项目根目录处运行 Mitar

```bash
mitar my_theorem.lean
```

3. 生成交互式 HTML 页面

### 其它命令行语法

```bash
mitar make <file.lean>                  # 生成 HTML 页面
mitar make <file.lean> -k               # 保留中间 JSON 文件
mitar make <file.lean> -t <ConfigDir>   # 额外加载自定义策略目录
mitar clean                             # 清理中间文件
```

---

## 配置指南

### 1. 步骤规则

你需要为每个策略编写一个规则配置文件 (`.toml`) , 每个文件同时描述该策略在
- Lean2TeX 中如何匹配
- Mitar 中如何展示

#### 基础配置

| 字段 | 类型 | 归属 | 简要说明 |
|---|---|---|---|
| `name` | `String` | 通用 | 策略唯一标识 |
| `syntax` | `String` | Lean2TeX | 用于匹配的策略语法 |
| `tag` | `String` | Mitar | 步骤标签名称 |
| `put_off` | `Bool` | Lean2TeX | 是否在策略执行后记录 (适用于产生新自由变量的策略) |
| `content` | `String` | Mitar | 无条件打印模版 |

__`syntax`__
- 字面词 (如 `unfold` , `at` 等) 须精确匹配
- `$label` 用于捕获一个 Lean 标识符作为参数 `label`
- 匹配遵循 **前缀 / 最长匹配** 优先

__`put_off`__
- 对于更改自由变量的策略, 请使用默认值 `false`
- 对于产生新自由变量的策略, 请将其设置为 `true`
- Lean2TeX 暂时不支持同时符合上述两则情形的策略, 建议使用其它策略分步代替之

__`content`__
- 使用 `${label}` 占位符引用 `syntax` 中捕获的参数 `label`
- 使用 `${goal}` 和 `${goal'}` 可分别用于捕获该策略执行前的目标和执行后的目标
- 使用转义字符 `$$` 打印 `$`

#### 完整示例

##### 简单策略 (`rw.toml`)

```toml
name = "rw"
syntax = "rw"
tag = "重写"
content = "根据等式的重写规则，该命题成立"
```

##### 带参数 + 条件分支 (`unfold.toml`)

```toml
name = "unfold"
syntax = "unfold $concept"
tag = "应用定义"
content = "根据${concept}的定义, 我们需要证明${goal'}"
```

#### 加载方式

```lean
#load_tactics mathlib                   -- load Mathlib tactic rules
#load_tactics_toml ".../my_tactics/"    -- load custom tactic rules
```

---

### 2. 表述规则

详见 __Lean2TeX 速览__

示例:

```lean
-- 常量
attribute [Lean2TeX "\\mathbb{N}" Unit] Nat
attribute [Lean2TeX "\\mathbb{Z}" Unit] Int

-- 二元运算符（@N = 第 N 个参数，1-indexed）
attribute [Lean2TeX "@5+@6" Add any any any any left right] HAdd.hAdd
attribute [Lean2TeX "@5^{@6}" Supscript any any any any base script] HPow.hPow
attribute [Lean2TeX "@1+1" Add left] Nat.succ  -- n.succ → n+1

-- 逻辑
attribute [Lean2TeX "@1且@2" Text any any] And
attribute [Lean2TeX "@1或@2" Text any any] Or

-- 解包包装函数
attribute [Lean2TeX_unwrap 1] OfNat.ofNat   -- 数字字面量
attribute [Lean2TeX_unwrap 2] Nat.cast       -- Nat → ℤ 转换
```

---

### 3. Mitar 高级配置

#### 条件打印模版

| 条件 | 触发时机 |
|---|---|
| `Final` | 终结步骤 |
| `NonFinal` | 非终结步骤 |
| `Contra` | 当前目标为"矛盾" |

- 无条件时直接写顶层 `content = "..."` , 会被后续条件覆盖 (条件按优先级从低到高排列, 后者覆盖前者)

使用示例:

```toml
content = "化简可得${goal'}"   -- 无条件时直接写 content

[NonFinal.Contra]
content = "由此推出矛盾"

[Final]
content = "综上得证"
```
