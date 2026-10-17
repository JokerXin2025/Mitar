# Lean2TeX（Python 重实现）

Mitar 页面生成器的语义渲染接口。接收 ProofScript 的 ExprJSON，先转换成内部
`DisplayNode` tree，再通过语义宏和布局规则输出 TeX：

```text
ExprJSON -> SemanticConverter -> DisplayTree -> MacroRegistry -> LayoutRenderer -> TeX
```

这是原 Lean2TeX 的 Python 语义重实现。宏配置使用 `config/macros.toml`，变量命名池
配置使用 `config/variable.toml`。

## 目录结构

```
Lean2TeX/
├── __init__.py           包入口（Expr2TeX / load / expr2tex 便捷函数）
├── model.py              DisplayNode、Macro、MacroStyle、RenderDiagnostic
├── semantic.py           ExprJSON -> DisplayTree（app 投影、绑定、fallback）
├── macros.py             新宏配置加载、alias、normalization 与验证
├── renderer.py           DisplayTree -> TeX（优先级、结合性、mode）
├── variable.py           变量分配器（三级 fallback + 名字池 + FVar 缓存）
├── core.py               公共 facade
├── config/
│   ├── macros.toml       新语义宏（0-based arguments + #N）
│   └── variable.toml     变量命名池（原 Variable.toml）
└── tests/
    ├── test_render.py    渲染回归测试
    └── test_semantic.py  转换、宏、布局、fallback 和诊断测试
```

## 用法

```python
from Lean2TeX import load

renderer = load()                 # 加载 macros.toml 等
renderer.reset()                  # 每个定理渲染前清空变量分配状态
tex = renderer.render(node, language="en")  # node 是 JSON 表达式子树
```

`render` 是 ExprJSON 到 TeX 的公共 facade；需要访问中间结构时使用 `convert` 与
`render_display`：

```python
display = renderer.convert(node)
tex = renderer.render_display(display)
```

也可用模块级便捷函数（惰性单例）：

```python
from Lean2TeX import expr2tex
tex = expr2tex(node)

# 模块级便捷入口也支持语言
tex = expr2tex(node, language="en")
```

## TOML 模板语法

新配置位于 `config/macros.toml`。ProofScript ExprJSON 提供 application argument 的
`isExplicit`/`isTypeclass`，核心宏使用 `arguments = "explicit"`。模板中的 `#N` 只引用
投影后的语义 children：

```toml
[[macro]]
name = "HAdd.hAdd"
kind = "operator"
arguments = "explicit"
styles = [
  { name = "formula", mode = "formula", template = "#0+#1", fixity = "infix", precedence = 65, associativity = "left" }
]
```

支持 `formula`/`text` mode、`fixity`、`precedence`、`associativity`，以及动态宏的
`#*` 和 `separator`。配置加载时会验证 style 唯一性、枚举值、参数索引和占位符。
英文 prose style 使用 `prose-en`，中文 prose style 使用 `prose-zh`；未配置英文 prose
时会回退到 `formula`。

```toml
[[constant]]
name = "HAdd.hAdd"
template = '@5+@6'
node = "Add"
roles = ["any", "any", "any", "any", "left", "right"]

[[unwrap]]
name = "OfNat.ofNat"
index = 1
```

## 公共接口

- `renderer.convert(expr)` 返回 `DisplayNode`；
- `renderer.render_display(display, style="formula")` 渲染 DisplayTree；
- `renderer.render(expr)` 保留旧入口；
- `renderer.render_relation(expr)` 为 calc 等上层规则提供关系符号；
- `renderer.diagnostics` 返回最近一次转换与渲染诊断。

未知常量显示为 `\\operatorname{shortName}`，未知 application 显示为
`f\\left(a,b\\right)`。lambda、let、projection、metavariable 和未知节点均有可见
fallback，不再静默输出空字符串。

## 交互式变量引用

公式变量通过 KaTeX `\\htmlData` 携带语义引用信息：

- 同一 fvar 根据 `fvarId` 在当前 theorem 内共享高亮组；
- binder 与对应 bvar 根据 `bindId`/`bindRef` 在当前 DisplayTree 内共享高亮组；
- 不同 proof step 独立转换的 binder 组彼此隔离；
- 原始 Lean 标识符写入 HTML data attribute 前会经过 hash。

`js/lean2tex.js` 在最近的 `.theorem-proof` 中高亮同组引用，binder 声明使用略有区别的
颜色。KaTeX trust 仅允许 `\\htmlData`，没有开放任意 trusted HTML command。

## 配置能力

`macros.toml` 已覆盖核心逻辑、算术、关系、集合和常见 Mathlib 投影常量。配置还支持：

- `alias`：将多个 Lean declaration 映射到同一个显示宏，并在加载时检测 cycle；
- `normalization`：支持 `select`、`rename`、`drop`、`reorder`；
- 动态宏：使用 `dynamic_arity = true`、`#*` 和 `separator`；
- layout 验证：检查 style、placeholder、参数和 precedence。

每次 Mitar 构建会在 `.Mitar/build/lean2tex-report.json` 输出 Lean2TeX 诊断，包括缺失
宏、fallback、参数越界和未知 ExprJSON 节点，并按错误码与缺失常量汇总。新版
ProofScript 已提供 application argument binder 信息，核心宏现已使用
`arguments = "explicit"`，所有 application 节点必须包含 ProofScript 导出的 arguments 描述。

## 边界

- 新 ExprJSON 使用逐节点 `isProp` 区分命题变量、证明变量和数据变量；
- 新 ExprJSON 的 `sourceRange` 会进入 DisplayTree metadata 和诊断报告；字段缺失时只保留
  ExprJSON child path，不猜测源码位置。
