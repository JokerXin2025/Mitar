import tempfile
import unittest
from pathlib import Path

from Mitar.Rules.media import render_figure, render_latex


class MediaRendererTest(unittest.TestCase):
    def test_latex_svg_is_embedded(self):
        rendered, diagnostics = render_latex({
            "metadata": {"title": "Diagram", "label": "diagram", "extra": []},
            "language": "latex", "source": "x^2", "svg": "<svg><script>x</script></svg>",
        })
        self.assertEqual(diagnostics, [])
        self.assertIn('id="figure-diagram"', rendered)
        self.assertIn('data:image/svg+xml;base64,', rendered)
        self.assertNotIn("<script>", rendered)
        self.assertIn('class="flip-btn page-media-flip-button"', rendered)
        self.assertIn('class="proof-flip-inner page-media-flip-inner"', rendered)
        self.assertIn('code-theme-light', rendered)
        self.assertIn('class="code-builtin code-theme-light"', rendered)
        encoded = rendered.split('base64,', 1)[1].split('"', 1)[0]
        import base64
        sanitized = base64.b64decode(encoded).decode("utf-8")
        self.assertNotIn("script", sanitized)

    def test_latex_svg_removes_active_content_and_external_urls(self):
        rendered, diagnostics = render_latex({
            "metadata": {"title": "Unsafe", "label": None, "extra": []},
            "language": "latex",
            "source": "x",
            "svg": '<svg xmlns="http://www.w3.org/2000/svg"><script>alert(1)</script><image href="https://example.com/x.png" onload="alert(1)"/><path style="fill:url(javascript:x)"/></svg>',
        })
        self.assertEqual(diagnostics, [])
        import base64
        encoded = rendered.split('base64,', 1)[1].split('"', 1)[0]
        sanitized = base64.b64decode(encoded).decode("utf-8")
        self.assertNotIn("script", sanitized)
        self.assertNotIn("https://", sanitized)
        self.assertNotIn("onload", sanitized)
        self.assertNotIn("javascript:", sanitized)

    def test_figure_resource_is_embedded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            image = root / "assets" / "image.png"
            image.parent.mkdir()
            image.write_bytes(b"\x89PNG\r\n")
            rendered, diagnostics = render_figure({
                "metadata": {"title": "Image", "label": "image", "extra": []},
                "path": "assets/image.png", "extension": "png",
            }, root)
        self.assertEqual(diagnostics, [])
        self.assertIn('data:image/png;base64,', rendered)
        self.assertIn('id="figure-image"', rendered)

    def test_latex_resource_is_embedded(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            resource = root / ".ProofScript" / "resources" / "svg" / "123.svg"
            resource.parent.mkdir(parents=True)
            resource.write_text("<svg><text>resource</text></svg>", encoding="utf-8")
            rendered, diagnostics = render_latex({
                "metadata": {"title": "Diagram", "label": "diagram", "extra": []},
                "language": "latex",
                "source": "x^2",
                "svg": {"$resource": {
                    "path": ".ProofScript/resources/svg/123.svg",
                    "hash": "123",
                    "mediaType": "image/svg+xml",
                    "encoding": "utf-8",
                }},
            }, root)

        self.assertEqual(diagnostics, [])
        self.assertIn("data:image/svg+xml;base64,", rendered)

    def test_invalid_resources_render_error(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            missing, missing_diagnostics = render_figure({
                "metadata": {"title": "Missing", "label": None, "extra": []},
                "path": "missing.png", "extension": "png",
            }, root)
            escaped, escaped_diagnostics = render_figure({
                "metadata": {"title": "Escaped", "label": None, "extra": []},
                "path": "../outside.png", "extension": "png",
            }, root)
        self.assertIn("page-media-error", missing)
        self.assertIn("page-media-error", escaped)
        self.assertEqual(missing_diagnostics[0]["kind"], "media-error")
        self.assertEqual(escaped_diagnostics[0]["kind"], "media-error")


if __name__ == "__main__":
    unittest.main()
