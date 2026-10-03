"""What the check of the CI runs with restricted CPU features rejects."""

import unittest

import check_cpu_feature_runs as check

WORKFLOW = """jobs:
  rust:
    steps:
      # VG_CPU_FEATURES in a comment is fine.
      - run: cargo test --locked
  rust-cpu-features:
    strategy:
      matrix:
        include:
          # x86-64.
          - chip: native
            arch: x86_64
            runs: |
              - | sha1 aes_gcm cpu
              aes,ssse3 | aes_gcm cpu
          - chip: native
            arch: x86
            container:
              image: rust:slim
              options: --platform linux/386
            runs: |
              - | sha1 cpu
              none | all
          - chip: icx
            runs: |
              - | ed25519 cpu
          - chip: icx
            part: AES-GCM
            runs: |
              aes,vaes | aes_gcm cpu
    name: Rust
    steps:
      - run: VG_CPU_FEATURES=$features cargo test
  coverage:
    steps: []
"""


class Check(unittest.TestCase):
    def assert_error(self, text, fragment):
        errs = check.errors(text)
        self.assertTrue(any(fragment in e for e in errs), errs)

    def test_the_workflow(self):
        self.assertEqual(check.errors(check.WORKFLOW.read_text()), [])

    def test_fixture(self):
        self.assertEqual(check.errors(WORKFLOW), [])
        found = check.entries(WORKFLOW)
        self.assertEqual(len(found), 4)
        self.assertEqual(found[1]["container.options"], "--platform linux/386")
        self.assertEqual([r for _, r in found[1]["runs"]], ["- | sha1 cpu", "none | all"])

    def test_set_outside_the_job(self):
        text = WORKFLOW.replace(
            "      - run: cargo test --locked\n",
            "      - run: cargo test --locked\n        env:\n          VG_CPU_FEATURES: none\n",
        )
        self.assert_error(text, "outside `rust-cpu-features`")

    def test_features_twice_on_a_cpu(self):
        # Another entry of the same CPU counts too.
        text = WORKFLOW.replace("aes,vaes | aes_gcm cpu", "- | aes_gcm cpu")
        self.assert_error(text, "VG_CPU_FEATURES=- again on this CPU")

    def test_same_features_on_other_cpus(self):
        text = WORKFLOW.replace("- | ed25519 cpu", "aes,ssse3 | ed25519 cpu")
        self.assertEqual(check.errors(text), [])

    def test_malformed_lines(self):
        self.assert_error(WORKFLOW.replace("none | all", "none all"), "not `<VG_CPU_FEATURES> | <tests>`")
        self.assert_error(WORKFLOW.replace("none | all", "none |"), "not `<VG_CPU_FEATURES> | <tests>`")
        self.assert_error(WORKFLOW.replace("none | all", "none | all sha1"), "`all` with other tests")
        self.assert_error(WORKFLOW.replace("- | sha1 cpu", "- | sha1 cpu sha1"), "a test named twice")


if __name__ == "__main__":
    unittest.main()
