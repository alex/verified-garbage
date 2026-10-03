"""What the Lean build's plan counts as changed; no builds."""

import pathlib
import tempfile
import unittest
from unittest import mock

import lean_shards as shards

LAKEFILE = """name = "VerifiedGarbage"
moreLeanArgs = ["-j2"]

[[lean_lib]]
name = "VerifiedGarbage"
globs = ["VerifiedGarbage.*"]

# Compiled specifications.
[[lean_lib]]
name = "NativeSpec"
roots = []
globs = ["VerifiedGarbage.Spec.A"]
precompileModules = true
"""


class LakefileInputs(unittest.TestCase):
    def test_comments_and_layout_change_nothing(self):
        other = LAKEFILE.replace("# Compiled specifications.\n", "").replace(
            'globs = ["VerifiedGarbage.Spec.A"]', 'globs = [\n  "VerifiedGarbage.Spec.A",\n]')
        self.assertEqual(shards.lakefile_inputs(other), shards.lakefile_inputs(LAKEFILE))

    def test_module_lists_are_not_settings(self):
        settings, libraries = shards.lakefile_inputs(LAKEFILE)
        added = LAKEFILE.replace('"VerifiedGarbage.Spec.A"]', '"VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"]')
        settings2, libraries2 = shards.lakefile_inputs(added)
        self.assertEqual(settings2, settings)
        self.assertEqual(libraries["NativeSpec"], ["globs:VerifiedGarbage.Spec.A"])
        self.assertEqual(libraries2["NativeSpec"], ["globs:VerifiedGarbage.Spec.A", "globs:VerifiedGarbage.Spec.B"])

    def test_settings(self):
        settings = shards.lakefile_inputs(LAKEFILE)[0]
        for old, new in [
            ('moreLeanArgs = ["-j2"]', 'moreLeanArgs = ["-j4"]'),
            ("precompileModules = true", "precompileModules = false"),
            ('name = "NativeSpec"', 'name = "NativeSpecs"'),
        ]:
            with self.subTest(new=new):
                self.assertNotEqual(shards.lakefile_inputs(LAKEFILE.replace(old, new))[0], settings)


class Matches(unittest.TestCase):
    closure = {"A": frozenset({"A", "B"})}

    def test_entries(self):
        for entry, module, expected in [
            ("globs:X.*", "X", True),
            ("globs:X.*", "X.Y.Z", True),
            ("globs:X.*", "XY", False),
            ("globs:X.+", "X", False),
            ("globs:X.+", "X.Y", True),
            ("globs:X.Y", "X.Y", True),
            ("globs:X.Y", "X.Y.Z", False),
            ("roots:A", "B", True),
            ("roots:A", "C", False),
            ("roots:C", "C", True),
        ]:
            with self.subTest(entry=entry, module=module):
                self.assertEqual(shards.matches(entry, module, self.closure), expected)


class Plan(unittest.TestCase):
    """`plan` on a small project, against the manifest of its build."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.lean = pathlib.Path(tmp.name)
        patch = mock.patch.object(shards, "LEAN", self.lean)
        patch.start()
        self.addCleanup(patch.stop)
        for name, text in {
            "lean-toolchain": "leanprover/lean4:v4.34.1\n",
            "lake-manifest.json": "{}\n",
            "lakefile.toml": LAKEFILE,
            "VerifiedGarbage.lean": "import VerifiedGarbage.Proof\n",
            "VerifiedGarbage/Spec/A.lean": "\n",
            "VerifiedGarbage/Spec/B.lean": "\n",
            "VerifiedGarbage/Proof.lean": "import VerifiedGarbage.Spec.A\nimport VerifiedGarbage.Spec.B\n",
            "VerifiedGarbage/Other.lean": "\n",
        }.items():
            (self.lean / name).parent.mkdir(parents=True, exist_ok=True)
            (self.lean / name).write_text(text)
        self.manifest = {
            "inputs": shards.inputs(),
            "sources": {m: shards.digest(f) for m, f in shards.modules().items()},
        }

    def stale(self):
        return shards.plan(self.manifest)["stale"]

    def edit(self, old, new):
        f = self.lean / "lakefile.toml"
        f.write_text(f.read_text().replace(old, new))

    def test_unchanged(self):
        self.assertEqual(self.stale(), 0)

    def test_adding_a_module_to_a_library(self):
        # Spec.B moves to NativeSpec: it, and what imports it, rebuild.
        self.edit('"VerifiedGarbage.Spec.A"]', '"VerifiedGarbage.Spec.A", "VerifiedGarbage.Spec.B"]')
        self.assertEqual(self.stale(), 3)

    def test_a_comment(self):
        self.edit("# Compiled specifications.", "# The compiled specifications.")
        self.assertEqual(self.stale(), 0)

    def test_a_setting_rebuilds_everything(self):
        self.edit('moreLeanArgs = ["-j2"]', 'moreLeanArgs = ["-j4"]')
        self.assertEqual(self.stale(), 5)

    def test_toolchain_rebuilds_everything(self):
        (self.lean / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        self.assertEqual(self.stale(), 5)

    def test_an_older_manifest_rebuilds_everything(self):
        self.manifest["inputs"] = {f: shards.digest(self.lean / f) for f in shards.INPUTS}
        self.assertEqual(self.stale(), 5)


if __name__ == "__main__":
    unittest.main()
