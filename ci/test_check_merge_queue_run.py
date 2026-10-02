"""Which merge queue runs a push to main reuses; no API calls."""

import io
import json
import subprocess
import unittest
from unittest import mock

import merge_queue_run as mq

REPO = "pyca/verified-garbage"
SHA = "a" * 40
WORKFLOW_ID = 42


def run(**changes) -> dict:
    r = {
        "id": 100,
        "event": "merge_group",
        "status": "completed",
        "conclusion": "success",
        "head_sha": SHA,
        "head_branch": "gh-readonly-queue/main/pr-7-" + "b" * 40,
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


class Find(unittest.TestCase):
    """`find` against fake API responses."""

    def responses(self, runs=None, artifacts=None):
        def fake(path):
            if path == f"repos/{REPO}/actions/runs/5":
                return {"workflow_id": WORKFLOW_ID}
            if path.startswith(f"repos/{REPO}/actions/workflows/{WORKFLOW_ID}/runs?"):
                return {"workflow_runs": [run()] if runs is None else runs}
            if path.startswith(f"repos/{REPO}/actions/runs/100/artifacts"):
                return {"artifacts": [{"name": "lean-build-final", "expired": False}] if artifacts is None else artifacts}
            raise subprocess.CalledProcessError(1, ["gh", "api", path])

        return mock.patch.object(mq, "gh", side_effect=fake)

    def find(self):
        with mock.patch("sys.stderr"):
            return mq.find(REPO, SHA, "5")

    def test_reuse(self):
        with self.responses():
            self.assertEqual(self.find(), 100)

    def test_no_run(self):
        with self.responses(runs=[]):
            self.assertIsNone(self.find())
        with self.responses(runs=[run(conclusion="failure")]):
            self.assertIsNone(self.find())

    def test_no_artifact(self):
        with self.responses(artifacts=[]):
            self.assertIsNone(self.find())

    def test_api_failure(self):
        with mock.patch.object(mq, "gh", side_effect=subprocess.CalledProcessError(1, "gh")):
            self.assertIsNone(self.find())
        with mock.patch.object(mq, "gh", side_effect=json.JSONDecodeError("x", "", 0)):
            self.assertIsNone(self.find())
        with mock.patch.object(mq, "gh", return_value={}):
            self.assertIsNone(self.find())

    def test_outputs(self):
        env = {"GITHUB_REPOSITORY": REPO, "GITHUB_SHA": SHA, "GITHUB_RUN_ID": "5"}
        for result, out in [(100, "run-id=100\n"), (None, "run-id=\n")]:
            with (
                self.subTest(result=result),
                mock.patch.dict("os.environ", env),
                mock.patch.object(mq, "find", return_value=result) as find,
                mock.patch("sys.stdout", new_callable=io.StringIO) as stdout,
            ):
                self.assertEqual(mq.main(), 0)
                find.assert_called_once_with(REPO, SHA, "5")
                self.assertEqual(stdout.getvalue(), out)


if __name__ == "__main__":
    unittest.main()
