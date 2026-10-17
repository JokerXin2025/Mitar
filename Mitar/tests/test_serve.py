import tempfile
import unittest
from pathlib import Path

from unittest.mock import patch

from Mitar.serve import MitarRequestHandler, local_ipv4_addresses


class ServeTest(unittest.TestCase):
    def test_wasm_and_module_mime_types(self):
        self.assertEqual(MitarRequestHandler.extensions_map[".wasm"], "application/wasm")
        self.assertEqual(MitarRequestHandler.extensions_map[".mjs"], "text/javascript")

    def test_demo_build_shape_required_by_server(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text('name = "Demo"', encoding="utf-8")
            build = root / ".Mitar/build"
            build.mkdir(parents=True)
            (build / "index.html").write_text("<!doctype html>", encoding="utf-8")
            self.assertTrue((build / "index.html").is_file())

    @patch("Mitar.serve.socket.getaddrinfo")
    def test_local_addresses_exclude_loopback_and_link_local(self, getaddrinfo):
        getaddrinfo.return_value = [
            (2, 1, 6, "", ("127.0.0.1", 0)),
            (2, 1, 6, "", ("192.168.1.8", 0)),
            (2, 1, 6, "", ("169.254.1.2", 0)),
            (2, 1, 6, "", ("198.18.0.1", 0)),
        ]
        with patch("Mitar.serve.socket.socket", side_effect=OSError):
            self.assertEqual(local_ipv4_addresses(), ["192.168.1.8"])


if __name__ == "__main__":
    unittest.main()
