"""Which merge queue runs a push to main reuses; no API calls."""

import io
import json
import subprocess
import unittest
from unittest import mock

import merge_queue_run as mq

REPO = "pyca/verified-garbage"
SHA = "a" * 40
BEFORE = "b" * 40
WORKFLOW_ID = 42


def run(**changes) -> dict:
    r = {
        "id": 100,
        "event": "merge_group",
        "status": "completed",
        "conclusion": "success",
        "head_sha": SHA,
        "head_branch": f"gh-readonly-queue/main/pr-7-{BEFORE}",
        "workflow_id": WORKFLOW_ID,
        "path": ".github/workflows/ci.yml",
        "repository": {"full_name": REPO},
        "head_repository": {"full_name": REPO},
    }
    r.update(changes)
    return r


class SelectRun(unittest.TestCase):
    def select(self, *runs):
        return mq.select_run(list(runs), REPO, SHA, WORKFLOW_ID)

    def test_qualifying_run(self):
        self.assertEqual(self.select(run()), 100)

    def test_newest_of_several(self):
        self.assertEqual(self.select(run(id=100), run(id=300), run(id=200)), 300)

    def test_none(self):
        self.assertIsNone(self.select())

    def test_each_condition_is_required(self):
        for changes in [
            {"event": "pull_request"},
            {"event": "push"},
            {"status": "in_progress"},
            {"conclusion": "failure"},
            {"conclusion": None},
            {"head_sha": "c" * 40},
            {"workflow_id": 43},
            {"path": ".github/workflows/bench.yml"},
            {"repository": {"full_name": "someone/verified-garbage"}},
            {"head_repository": {"full_name": "someone/verified-garbage"}},
            {"head_repository": None},
            {"head_branch": "main"},
            {"head_branch": "gh-readonly-queue/other/pr-7"},
            {"head_branch": None},
        ]:
            with self.subTest(changes=changes):
                self.assertIsNone(self.select(run(**changes)))
                # A disqualified run never hides a qualifying one.
                self.assertEqual(self.select(run(id=999, **changes), run()), 100)

    def test_path_with_ref(self):
        self.assertEqual(self.select(run(path=".github/workflows/ci.yml@refs/heads/main")), 100)


class FinalArtifact(unittest.TestCase):
    def test_present(self):
        self.assertTrue(mq.has_final_artifact([{"name": "lean-build-final", "expired": False}]))

    def test_expired_missing_or_other(self):
        for artifacts in [
            [],
            [{"name": "lean-build-final", "expired": True}],
            [{"name": "lean-build-final"}],
            [{"name": "lean-build-1", "expired": False}],
        ]:
            with self.subTest(artifacts=artifacts):
                self.assertFalse(mq.has_final_artifact(artifacts))


class RustInputs(unittest.TestCase):
    def test_feeds_rust_cache(self):
        for path in [
            "Cargo.toml",
            "Cargo.lock",
            "bench/Cargo.toml",
            "rust-toolchain",
            "rust-toolchain.toml",
            ".cargo/config.toml",
            "sub/.cargo/config",
            ".github/workflows/ci.yml",
        ]:
            with self.subTest(path=path):
                self.assertTrue(mq.feeds_rust_cache(path))
        for path in ["src/lib.rs", "src/asm/x86_64/sha256.rs", "lean/lakefile.toml", "MyCargo.toml", "", "x.cargo/y"]:
            with self.subTest(path=path):
                self.assertFalse(mq.feeds_rust_cache(path))

    def compare(self, *files, status="ahead"):
        return {"status": status, "files": [{"filename": f} for f in files]}

    def test_unchanged(self):
        self.assertFalse(mq.rust_inputs_changed(self.compare("src/lib.rs", "lean/VerifiedGarbage/Spec/Foo.lean")))

    def test_changed(self):
        self.assertTrue(mq.rust_inputs_changed(self.compare("src/lib.rs", "Cargo.lock")))

    def test_renamed_from_an_input(self):
        c = {"status": "ahead", "files": [{"filename": "old.toml", "previous_filename": "Cargo.toml"}]}
        self.assertTrue(mq.rust_inputs_changed(c))

    def test_in_doubt(self):
        for c in [
            self.compare("src/lib.rs", status="diverged"),
            self.compare(status="identical"),
            self.compare(*[f"src/{i}.rs" for i in range(mq.MAX_COMPARE_FILES)]),
            {"status": "ahead"},
            {},
        ]:
            with self.subTest(c=c):
                self.assertTrue(mq.rust_inputs_changed(c))


class Find(unittest.TestCase):
    """`find` against fake API responses."""

    def responses(self, runs=None, artifacts=None, compare=None):
        def fake(path):
            if path == f"repos/{REPO}/actions/runs/5":
                return {"workflow_id": WORKFLOW_ID}
            if path.startswith(f"repos/{REPO}/actions/workflows/{WORKFLOW_ID}/runs?"):
                return {"workflow_runs": [run()] if runs is None else runs}
            if path.startswith(f"repos/{REPO}/actions/runs/100/artifacts"):
                return {"artifacts": [{"name": "lean-build-final", "expired": False}] if artifacts is None else artifacts}
            if path == f"repos/{REPO}/compare/{BEFORE}...{SHA}":
                if isinstance(compare, Exception):
                    raise compare
                return compare or {"status": "ahead", "files": [{"filename": "src/lib.rs"}]}
            raise subprocess.CalledProcessError(1, ["gh", "api", path])

        return mock.patch.object(mq, "gh", side_effect=fake)

    def find(self, before=BEFORE):
        with mock.patch("sys.stderr"):
            return mq.find(REPO, SHA, "5", before)

    def test_reuse_and_skip_rust(self):
        with self.responses():
            self.assertEqual(self.find(), (100, True))

    def test_reuse_with_rust(self):
        with self.responses(compare={"status": "ahead", "files": [{"filename": "Cargo.lock"}]}):
            self.assertEqual(self.find(), (100, False))
        with self.responses():
            self.assertEqual(self.find(before=mq.ZERO_SHA), (100, False))
        with self.responses(compare=subprocess.CalledProcessError(1, "gh")):
            self.assertEqual(self.find(), (100, False))

    def test_no_run(self):
        with self.responses(runs=[]):
            self.assertEqual(self.find(), (None, False))
        with self.responses(runs=[run(conclusion="failure")]):
            self.assertEqual(self.find(), (None, False))

    def test_no_artifact(self):
        with self.responses(artifacts=[]):
            self.assertEqual(self.find(), (None, False))

    def test_api_failure(self):
        with mock.patch.object(mq, "gh", side_effect=subprocess.CalledProcessError(1, "gh")):
            self.assertEqual(self.find(), (None, False))
        with mock.patch.object(mq, "gh", side_effect=json.JSONDecodeError("x", "", 0)):
            self.assertEqual(self.find(), (None, False))
        with mock.patch.object(mq, "gh", return_value={}):
            self.assertEqual(self.find(), (None, False))

    def test_outputs(self):
        env = {"GITHUB_REPOSITORY": REPO, "GITHUB_SHA": SHA, "GITHUB_RUN_ID": "5", "BEFORE": BEFORE}
        for result, out in [
            ((100, True), "run-id=100\nskip-rust=true\n"),
            ((None, False), "run-id=\nskip-rust=false\n"),
        ]:
            with (
                self.subTest(result=result),
                mock.patch.dict("os.environ", env),
                mock.patch.object(mq, "find", return_value=result) as find,
                mock.patch("sys.stdout", new_callable=io.StringIO) as stdout,
            ):
                self.assertEqual(mq.main(), 0)
                find.assert_called_once_with(REPO, SHA, "5", BEFORE)
                self.assertEqual(stdout.getvalue(), out)


if __name__ == "__main__":
    unittest.main()
