"""Lean2TeX 渲染引擎的测试。

用手工构造的 ProofScript 表达式 AST 验证 `Expr2TeX.render` 的渲染结果。

运行方式（在 Mitar 根目录）：

    python3 -m unittest Lean2TeX.tests.test_render -v

或直接：

    python3 Lean2TeX/tests/test_render.py
"""

from __future__ import annotations

import sys
import re
import unittest
from pathlib import Path

# 确保能 import Lean2TeX（从 Mitar 根或 Lean2TeX 包内运行均可）
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from Lean2TeX import load  # noqa: E402


_HTML_DATA = re.compile(r"\\htmlData\{[^{}]+\}\{([^{}]*)\}")


def _without_html_data(tex: str) -> str:
    return _HTML_DATA.sub(r"\1", tex)

# ── 手工构造 AST 的辅助函数 ──────────────────────────────────────────────────

def _const(name: str) -> dict:
    return {"kind": "const", "name": name, "levels": [], "isProp": False}


def _app(fn: dict, arg: dict) -> dict:
    return {"kind": "app", "fn": fn, "arg": arg}


def _fvar(name: str, typ: str) -> dict:
    if typ == "prop":
        t = {"kind": "sort", "level": {"kind": "level.zero"}}
    elif typ == "nat":
        t = _const("Nat")
    else:
        t = _const(typ)
    return {"kind": "fvar", "name": name, "id": name, "type": t, "isProp": typ == "prop"}


def _apply(const_name: str, *args: dict) -> dict:
    """构造 `const_name arg1 arg2 ...` 的应用链。"""
    node = _const(const_name)
    for a in args:
        node = _app(node, a)
    node["headConstant"] = const_name
    hidden = {
        "HAdd.hAdd": 4, "HSub.hSub": 4, "HMul.hMul": 4,
        "HDiv.hDiv": 4, "HPow.hPow": 4, "Eq": 1,
    }.get(const_name, 0)
    node["arguments"] = [
        {"expr": arg, "binderInfo": "implicit" if i < hidden else "default", "isExplicit": i >= hidden, "isTypeclass": False}
        for i, arg in enumerate(args)
    ]
    return node


class TestRender(unittest.TestCase):
    """核心渲染场景验证（对应原 Lean2TeX 的 Expr2TeX 行为）。"""

    @classmethod
    def setUpClass(cls):
        cls.renderer = load()

    def _render(self, node: dict | None, language="zh") -> str:
        assert node is not None
        self.renderer.reset()
        return _without_html_data(self.renderer.render(node, role="only", parent="Text", styles=("Root",), language=language))

    def test_arith_add_eq(self):
        """`n + 0 = n` → `n+0=n`（HAdd 模板 @5+@6 + OfNat unwrap + Eq 模板）。"""
        nat = _const("Nat")
        n = _fvar("n", "nat")
        zero = {"kind": "lit", "lit": {"kind": "literal.nat", "value": 0}}
        add = _apply("HAdd.hAdd", nat, nat, nat, _const("instAddNat"), n, zero)
        tex = self._render(_apply("Eq", nat, add, n))
        self.assertEqual(tex.strip(), "$n+0=n$")

    def test_eq_relation(self):
        """`a = b`（Nat 变量）→ 走 Nat 名字池，依次分配 n、m，渲染 `n=m`。"""
        node = _apply("Eq", _const("Nat"), _fvar("a", "nat"), _fvar("b", "nat"))
        self.assertEqual(self._render(node).strip(), "$n=m$")

    def test_prop_pool_global_unique(self):
        """命题变量走 Prop 名字池：三个 `Prop` fvar 依次分配 P、Q、R（全局唯一）。"""
        p = _fvar("A", "prop")
        q = _fvar("B", "prop")
        r = _fvar("C", "prop")
        node = _apply("And", p, _apply("And", q, r))
        self.assertEqual(self._render(node).strip(), "$P$ 且 $Q$ 且 $R$")

    def test_exists_word(self):
        """`∃ n : Nat, n = 0` → 中文「存在 … 使得 …」表述。"""
        lit0 = {"kind": "lit", "lit": {"kind": "literal.nat", "value": 0}}
        bvar0 = {"kind": "bvar", "index": 0}
        body = _apply("Eq", _const("Nat"), bvar0, lit0)
        lam = {"kind": "lam", "name": "n", "type": _const("Nat"), "body": body, "binderInfo": "default"}
        node = _apply("Exists", _const("Nat"), lam)
        tex = self._render(node)
        self.assertIn("存在", tex)
        self.assertIn("使得", tex)
        self.assertIn("\\mathbb{N}", tex)

    def test_and_word(self):
        """`And P Q` → 中文「且」连接（命题变量 P/Q 直接渲染其名字）。"""
        node = _apply("And", _fvar("P", "prop"), _fvar("Q", "prop"))
        self.assertEqual(self._render(node).strip(), "$P$ 且 $Q$")

    def test_or_word(self):
        """`Or P Q` → 中文「或」连接。"""
        node = _apply("Or", _fvar("P", "prop"), _fvar("Q", "prop"))
        self.assertEqual(self._render(node).strip(), "$P$ 或 $Q$")

    def test_not_word(self):
        """`Not P` → 「命题…不成立」。"""
        node = _apply("Not", _fvar("P", "prop"))
        self.assertEqual(self._render(node).strip(), "命题 $P$ 不成立")

    def test_iff_word(self):
        """`Iff P Q` → 中文「当且仅当」连接。"""
        node = _apply("Iff", _fvar("P", "prop"), _fvar("Q", "prop"))
        self.assertEqual(self._render(node).strip(), "$P$ 当且仅当 $Q$")

    def test_english_logic_words(self):
        node = _apply("And", _fvar("P", "prop"), _apply("Or", _fvar("Q", "prop"), _fvar("R", "prop")))
        tex = self._render(node, language="en")
        self.assertIn("and", tex)
        self.assertIn("or", tex)

    def test_english_exists_word(self):
        body = _apply("Eq", _const("Nat"), {"kind": "bvar", "index": 0}, {"kind": "lit", "lit": {"kind": "literal.nat", "value": 0}})
        lam = {"kind": "lam", "name": "n", "type": _const("Nat"), "body": body, "binderInfo": "default"}
        tex = self._render(_apply("Exists", _const("Nat"), lam), language="en")
        self.assertIn("there exists", tex)
        self.assertIn("such that", tex)

    def test_implies_symbol(self):
        """`P → Q`（forall 箭头）→ `\\implies` 符号形式。"""
        node = {
            "kind": "forall",
            "name": "_",
            "type": _fvar("P", "prop"),
            "body": _fvar("Q", "prop"),
            "binderInfo": "default",
        }
        tex = self._render(node)
        self.assertIn("\\implies", tex)

    def test_unwrap_of_nat(self):
        """`OfNat.ofNat Nat 0 inst` unwrap 到字面量 `0`。"""
        lit0 = {"kind": "lit", "lit": {"kind": "literal.nat", "value": 0}}
        inst = _apply("instOfNatNat", lit0)
        node = _apply("OfNat.ofNat", _const("Nat"), lit0, inst)
        self.assertEqual(self._render(node).strip(), "$0$")


if __name__ == "__main__":
    unittest.main(verbosity=2)
