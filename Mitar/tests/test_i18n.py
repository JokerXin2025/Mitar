import unittest

from Mitar.i18n import strategy_tag, tr


class LanguageTest(unittest.TestCase):
    def test_strategy_tags_are_loaded_from_toml(self):
        self.assertEqual(strategy_tag("induction", "en"), "By induction,")
        self.assertEqual(strategy_tag("by_cases", "en"), "By cases,")
        self.assertEqual(strategy_tag("induction", "zh"), "数学归纳法")

    def test_page_catalog_has_both_languages(self):
        self.assertEqual(tr("page.references", "zh"), "参考文献")
        self.assertEqual(tr("page.references", "en"), "References")
        self.assertEqual(tr("language.switch", "en"), "Switch language")
