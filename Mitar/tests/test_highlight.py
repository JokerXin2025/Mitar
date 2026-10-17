import html
import unittest
from unittest.mock import patch

from Mitar.highlight import highlight_code


class HighlightTest(unittest.TestCase):
    def test_lean_highlighting_uses_mitar_classes(self):
        source = "theorem demo (n : Nat) : n + 0 = n := by\n  rfl -- done\n"
        rendered, applied = highlight_code(source, "lean4")

        self.assertTrue(applied)
        self.assertIn('<span class="code-keyword code-theme-dark">theorem</span>', rendered)
        self.assertIn('<span class="code-number code-theme-dark">0</span>', rendered)
        self.assertIn('<span class="code-comment code-theme-dark">-- done</span>', rendered)
        self.assertNotIn("class=\"k\"", rendered)
        self.assertEqual(_plain_text(rendered), source)

    def test_other_pygments_lexer(self):
        source = 'def greet(name):\n    return f"Hello, {name}"\n'
        rendered, applied = highlight_code(source, "python")

        self.assertTrue(applied)
        self.assertIn("code-keyword", rendered)
        self.assertIn("code-function", rendered)
        self.assertIn("code-string", rendered)
        self.assertEqual(_plain_text(rendered), source)

    def test_unknown_language_falls_back_to_escaped_plain_text(self):
        source = '<tag attribute="value">& text'
        rendered, applied = highlight_code(source, "not-a-real-language")

        self.assertFalse(applied)
        self.assertEqual(rendered, html.escape(source))
        self.assertNotIn("<span", rendered)

    def test_missing_pygments_falls_back_to_plain_text(self):
        with patch("Mitar.highlight.get_lexer_by_name", None):
            rendered, applied = highlight_code("a < b", "python")

        self.assertFalse(applied)
        self.assertEqual(rendered, "a &lt; b")


def _plain_text(rendered):
    from html.parser import HTMLParser

    class TextParser(HTMLParser):
        def __init__(self):
            super().__init__()
            self.parts = []

        def handle_data(self, data):
            self.parts.append(data)

        def handle_entityref(self, name):
            self.parts.append(f"&{name};")

        def handle_charref(self, name):
            self.parts.append(f"&#{name};")

    parser = TextParser()
    parser.feed(rendered)
    return "".join(parser.parts)


if __name__ == "__main__":
    unittest.main()
