"""Lean2TeX —— Mitar 页面生成器的 TeX 直译接口。

Lean2TeX 是 Mitar 的 Python 语义渲染模块。ProofScript 将 Lean 表达式导出为与 Lean
语法树同构的 ExprJSON，本模块将其转换为 DisplayTree，再渲染为 TeX。因此本模块的职责是：

    **接收证明树的一个子树（JSON 表达式 AST），输出对应的 TeX 代码。**

宏配置使用 `config/macros.toml`，变量命名池配置使用 `config/variable.toml`。

典型用法（作为 Mitar 的接口）：

    from Lean2TeX import load

    renderer = load()                          # 加载 macros.toml 和 variable.toml
    tex = renderer.render(node)                # node 是 JSON 表达式子树
    display = renderer.convert(node)
    tex = renderer.render_display(display)

每个定理渲染前应调用 `renderer.reset()` 清空变量分配状态（对应原 `resetVarAllocator`）。
"""

from __future__ import annotations

from .core import Expr2TeX, auto_wrap, load
from .expr import flatten_app
from .macros import MacroRegistry, load_macros_toml
from .model import DisplayNode, Macro, MacroStyle, Normalization, RenderDiagnostic
from .semantic import SemanticConverter
from .variable import (
    VarTypeConfig,
    VariableAllocator,
)

__all__ = [
    # 核心接口
    "Expr2TeX",
    "load",
    "auto_wrap",
    "expr2tex",
    "DisplayNode",
    "RenderDiagnostic",
    "SemanticConverter",
    "Macro",
    "MacroStyle",
    "Normalization",
    "MacroRegistry",
    "load_macros_toml",
    "flatten_app",
    # 变量系统
    "VariableAllocator",
    "VarTypeConfig",
]

# 模块级惰性单例：供 `expr2tex` 便捷函数复用（避免每次调用重复读 TOML）
_default_renderer: Expr2TeX | None = None


def expr2tex(
    node: dict,
    role: str = "only",
    parent: str = "Text",
    styles: tuple[str, ...] = ("Root",),
    language: str = "zh",
) -> str:
    """用默认配置渲染一个 JSON 表达式子树为 TeX 字符串。

    便捷入口，等价于 `load().render(node)`。内部使用惰性单例，后续调用复用。

    注意：单例的变量分配状态跨调用累积；渲染**多个定理**时应改用 `load()` 拿到独立
    渲染器并在每个定理前调用 `reset()`。
    """
    global _default_renderer
    if _default_renderer is None:
        _default_renderer = load()
    return _default_renderer.render(node, role, parent, styles, language=language)
