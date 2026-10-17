import unittest
import tempfile
from pathlib import Path

from Mitar.Rules import Initialize
from Mitar.engine import ProofEngine
from Mitar.strategy import STRATEGIES, load_strategy_configs


class StrategyConfigTest(unittest.TestCase):
    def test_tactic_language_blocks_provide_content(self):
        Initialize()
        proof = ProofEngine([
            {"_goal_": {"kind": "const", "name": "True", "isProp": True}},
            {"_step_": "trivial"},
        ])
        rendered = proof.render(proof.data, ["Global"])
        self.assertIn("显然", rendered)

    def test_all_strategy_configs_have_render_kinds_and_bilingual_templates(self):
        self.assertEqual(set(STRATEGIES), {
            "induction", "complete_induction", "by_cases", "by_contra", "intro_contra",
            "split_and", "split_suffice_necess", "split_exist_unique", "witness",
            "cases_by", "cases_by!", "cases_on", "contra", "split_and!", "split_iff",
            "constructor", "constructor!",
        })
        for config in STRATEGIES.values():
            self.assertTrue(config.kind)
            self.assertIn("zh", config.languages)
            self.assertIn("en", config.languages)
            self.assertIn("tag", config.languages["zh"])
            self.assertIn("tag", config.languages["en"])

    def test_strategy_nodes_are_loaded_from_toml(self):
        configs = load_strategy_configs()
        self.assertEqual(configs["induction"].nodes, ("zero", "succ"))
        self.assertEqual(configs["by_cases"].nodes, ("caseI", "caseII"))
        self.assertEqual(configs["split_and"].kind, "decompose")
        self.assertEqual(configs["witness"].nodes, ("data", "proof"))
        self.assertTrue(configs["split_and!"].dynamic_nodes)

    def test_invalid_strategy_kind_fails_at_load(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.toml"
            path.write_text('[strategy]\nname = "bad"\nkind = "unknown"\n', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "STR002"):
                load_strategy_configs(Path(directory))

    def test_missing_strategy_template_fails_at_load(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.toml"
            path.write_text('''[strategy]
name = "bad"
kind = "cases"
nodes = ["left", "right"]
[language.zh]
tag = "分类讨论"
[language.en]
tag = "By cases,"
''', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "STR005"):
                load_strategy_configs(Path(directory))

    def test_dynamic_strategy_renders_all_recorded_branches(self):
        Initialize()
        proof = ProofEngine([
            {"_goal_": {"kind": "const", "name": "True", "isProp": True}},
            {
                "name": "split_and!",
                "info": {},
                "goalI": [
                    {"_goal_": {"kind": "const", "name": "True", "isProp": True}},
                    {"_step_": "trivial"},
                ],
                "goalII": [
                    {"_goal_": {"kind": "const", "name": "True", "isProp": True}},
                    {"_step_": "trivial"},
                ],
                "goalIII": [
                    {"_goal_": {"kind": "const", "name": "True", "isProp": True}},
                    {"_step_": "trivial"},
                ],
            },
        ])

        rendered = proof.make("dynamic", "test.lean", 1, "")

        self.assertIn("递归拆分合取", rendered)
        self.assertIn("子目标 III", rendered)
        self.assertNotIn("未知策略", rendered)
