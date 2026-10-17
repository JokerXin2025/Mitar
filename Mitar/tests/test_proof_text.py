import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace

from Mitar.Rules.proof_text import ProofTextRenderer


def text(value):
    return {"text": {"value": value}}


class ProofTextRendererTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.build_root = Path(self.temp.name)
        target = SimpleNamespace(
            output_path = Path("Other/Module.html"),
            anchor = "theorem-result",
        )
        self.renderer = ProofTextRenderer(
            {("theorem", "result"): target},
            self.build_root,
            Path("Paper/Main.html"),
        )

    def tearDown(self):
        self.temp.cleanup()

    def test_all_inline_kinds(self):
        content = [
            text("plain $not-math$ <tag>"),
            {"strong": {"content": [text("strong")]}},
            {"emphasis": {"content": [text("emphasis")]}},
            {"strongEmphasis": {"content": [text("both")]}},
            {"code": {"value": "<code>"}},
            {"strike": {"content": [text("strike")]}},
            {"underline": {"content": [text("underline")]}},
            {"highlight": {"content": [text("highlight")]}},
            {"superscript": {"content": [text("sup")]}},
            {"subscript": {"content": [text("sub")]}},
            {"link": {"content": [text("safe")], "url": "https://example.com?a=1&b=2"}},
            {"link": {"content": [text("unsafe")], "url": "javascript:alert(1)"}},
            {"reference": {"kind": "theorem", "label": "result"}},
            {"reference": {"kind": "figure", "label": "missing"}},
            {"math": {"latex": "x < y"}},
            {"softBreak": {}},
            {"hardBreak": {}},
        ]
        rendered = self.renderer.render({"blocks": [{"paragraph": {"content": content}}]})

        self.assertIn('<span class="proof-text-literal">plain $not-math$ &lt;tag&gt;</span>', rendered)
        self.assertIn("<strong>", rendered)
        self.assertIn("<em>", rendered)
        self.assertIn("<strong><em>", rendered)
        self.assertIn("<code>&lt;code&gt;</code>", rendered)
        self.assertIn("<s>", rendered)
        self.assertIn("<u>", rendered)
        self.assertIn("<mark>", rendered)
        self.assertIn("<sup>", rendered)
        self.assertIn("<sub>", rendered)
        self.assertIn('href="https://example.com?a=1&amp;b=2"', rendered)
        self.assertIn('href="#"', rendered)
        self.assertIn('../Other/Module.html#theorem-result', rendered)
        self.assertIn("unresolved-reference", rendered)
        self.assertIn("$x &lt; y$", rendered)
        self.assertIn("\n", rendered)
        self.assertIn("<br>", rendered)

    def test_all_block_kinds_and_nested_content(self):
        blocks = [
            {"heading": {"level": 1, "label": "intro", "content": [text("Intro")]}},
            {"heading": {"level": 9, "label": None, "content": [text("Clamped")]}},
            {"code": {"language": "lean<script>", "source": "theorem x : True := by\n  trivial <&>"}},
            {"code": {"language": None, "source": "plain"}},
            {"unorderedList": {"items": [
                {"ordinal": None, "content": [{"paragraph": {"content": [text("item")]}}]},
            ]}},
            {"orderedList": {"start": 3, "items": [
                {"ordinal": None, "content": [{"paragraph": {"content": [text("third")]}}]},
                {"ordinal": 8, "content": [{"quote": {"content": [
                    {"paragraph": {"content": [text("eighth")]}}
                ]}}]},
            ]}},
            {"displayMath": {"latex": "x^2 & y"}},
        ]
        rendered = self.renderer.render({"source": "ignored", "blocks": blocks})

        self.assertTrue(rendered.startswith('<section class="proof-text-card">'))
        self.assertIn('class="flip-btn proof-text-flip-button"', rendered)
        self.assertIn('class="proof-flip-inner proof-text-flip-inner"', rendered)
        self.assertIn("ignored", rendered)
        self.assertIn('<h1 id="heading-intro">', rendered)
        self.assertIn("<h4>", rendered)
        self.assertIn('data-language="lean&lt;script&gt;"', rendered)
        self.assertIn('class="language-lean-script-"', rendered)
        self.assertIn("trivial &lt;&amp;&gt;", rendered)
        self.assertIn('<pre class="page-code"><code>plain</code></pre>', rendered)
        self.assertIn("<ul><li>", rendered)
        self.assertIn('<ol start="3">', rendered)
        self.assertIn('<li value="8"><blockquote>', rendered)
        self.assertIn('<div class="display-math">$$x^2 &amp; y$$</div>', rendered)

    def test_known_code_language_is_highlighted(self):
        rendered = self.renderer.render({"blocks": [{
            "code": {"language": "lean4", "source": "theorem demo : True := by\n  trivial"}
        }]})

        self.assertIn('class="page-code code-highlighted"', rendered)
        self.assertIn('data-language="lean4"', rendered)
        self.assertIn('class="language-lean4"', rendered)
        self.assertIn('class="code-keyword code-theme-dark">theorem</span>', rendered)

    def test_unknown_code_language_uses_plain_text_fallback(self):
        rendered = self.renderer.render({"blocks": [{
            "code": {"language": "unknown-demo-language", "source": "<tag>&"}
        }]})

        self.assertIn('class="page-code"', rendered)
        self.assertNotIn("code-highlighted", rendered)
        self.assertIn("&lt;tag&gt;&amp;", rendered)


if __name__ == "__main__":
    unittest.main()
