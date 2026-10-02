#!/usr/bin/env python3
"""Finds the merge queue's CI run of the commit a push moved `main` to.

GitHub moves `main` to exactly the commit its merge queue tested, so a push
to `main` would re-run what the merge queue's run of that commit already
ran: the same code, with the same workflow. That run could restore only
`main`'s caches (and its own branch's, which start empty), so its outputs
are what this run would compute itself, and this run reuses them (see
`reuse` in .github/workflows/ci.yml). A run qualifies only if all of these
hold: it ran for `merge_group` on this repository's merge queue for `main`,
it succeeded, it tested this commit, it ran this workflow, and its final Lean
job's outputs are still there to download. Nothing from a pull request's run
qualifies.

The Rust jobs re-test too, but they also save `Swatinem/rust-cache`'s caches,
which only `main` saves, and which it saves only when the cache's key
changed. So they still run when a file the key hashes changed in the push
(see `feeds_rust_cache`).

Prints the `reuse` job's outputs, for `$GITHUB_OUTPUT`:

  run-id=ID          the run to reuse, or empty to run everything
  skip-rust=BOOL     whether the Rust jobs can be skipped

Reads `GITHUB_REPOSITORY`, `GITHUB_SHA`, `GITHUB_RUN_ID` and `BEFORE` (the
commit `main` was at before the push), and calls the API with `gh api`
(authenticated by `GH_TOKEN`). If anything goes wrong it warns and finds no
run, so the push runs everything, as it would without the merge queue.
"""

import json
import os
import subprocess
import sys

WORKFLOW = ".github/workflows/ci.yml"
# The branches GitHub's merge queue for `main` creates.
QUEUE_BRANCH = "gh-readonly-queue/main/"
# The artifact the `lean` job uploads last in the merge queue.
FINAL_ARTIFACT = "lean-build-final"
# The compare API lists at most this many files.
MAX_COMPARE_FILES = 300
ZERO_SHA = "0" * 40


def gh(path: str) -> dict:
    out = subprocess.run(["gh", "api", path], check=True, capture_output=True, text=True).stdout
    return json.loads(out)


def select_run(runs: list[dict], repo: str, sha: str, workflow_id: int) -> int | None:
    """The newest of `runs` that tested `sha` in `repo`'s merge queue for
    `main`, with this workflow, and succeeded."""
    ids = [
        r["id"]
        for r in runs
        if r.get("event") == "merge_group"
        and r.get("status") == "completed"
        and r.get("conclusion") == "success"
        and r.get("head_sha") == sha
        and r.get("workflow_id") == workflow_id
        and str(r.get("path", "")).split("@")[0] == WORKFLOW
        and (r.get("repository") or {}).get("full_name") == repo
        and (r.get("head_repository") or {}).get("full_name") == repo
        and str(r.get("head_branch", "")).startswith(QUEUE_BRANCH)
    ]
    return max(ids, default=None)


def has_final_artifact(artifacts: list[dict]) -> bool:
    """Whether the final Lean job's outputs can still be downloaded: runs
    from before it uploaded them have none, and artifacts expire."""
    return any(a.get("name") == FINAL_ARTIFACT and a.get("expired") is False for a in artifacts)


def feeds_rust_cache(path: str) -> bool:
    """Whether `path` is a file that `Swatinem/rust-cache` hashes into its
    key (its `src/config.ts`): any `Cargo.toml`, `Cargo.lock`,
    `rust-toolchain(.toml)` or `.cargo/` file (more than the workspace's,
    to be safe), or this workflow, which sets the toolchains and the
    `CARGO*`/`RUST*` environment variables the key also hashes."""
    name = path.rsplit("/", 1)[-1]
    return (
        name in ("Cargo.toml", "Cargo.lock", "rust-toolchain", "rust-toolchain.toml")
        or "/.cargo/" in "/" + path
        or path == WORKFLOW
    )


def rust_inputs_changed(compare: dict) -> bool:
    """Whether the comparison of `main` before and after the push may have
    changed a file the Rust caches' keys hash; when in doubt, it did."""
    files = compare.get("files")
    if compare.get("status") != "ahead" or not isinstance(files, list) or len(files) >= MAX_COMPARE_FILES:
        return True
    return any(feeds_rust_cache(f.get("filename", "")) or feeds_rust_cache(f.get("previous_filename", "")) for f in files)


def warn(message: str) -> None:
    print(f"::warning::{message}", file=sys.stderr)


def find(repo: str, sha: str, run_id: str, before: str) -> tuple[int | None, bool]:
    try:
        workflow_id = gh(f"repos/{repo}/actions/runs/{run_id}")["workflow_id"]
        runs = gh(
            f"repos/{repo}/actions/workflows/{workflow_id}/runs"
            f"?event=merge_group&head_sha={sha}&status=success&per_page=100"
        )["workflow_runs"]
        run = select_run(runs, repo, sha, workflow_id)
        if run is None:
            print(f"No successful merge queue run of {sha}: running everything.", file=sys.stderr)
            return None, False
        artifacts = gh(f"repos/{repo}/actions/runs/{run}/artifacts?name={FINAL_ARTIFACT}")["artifacts"]
        if not has_final_artifact(artifacts):
            warn(f"Run {run} has no {FINAL_ARTIFACT} to reuse: running everything.")
            return None, False
    except Exception as e:  # Any failure: run everything.
        warn(f"Could not look up the merge queue's run of {sha} ({e}): running everything.")
        return None, False
    print(f"Reusing run {run} of {sha}.", file=sys.stderr)
    try:
        changed = before == ZERO_SHA or rust_inputs_changed(gh(f"repos/{repo}/compare/{before}...{sha}"))
    except Exception as e:
        warn(f"Could not compare {before} with {sha} ({e}): running the Rust jobs.")
        changed = True
    return run, not changed


def main() -> int:
    run, skip_rust = find(
        os.environ["GITHUB_REPOSITORY"],
        os.environ["GITHUB_SHA"],
        os.environ["GITHUB_RUN_ID"],
        os.environ.get("BEFORE", "") or ZERO_SHA,
    )
    print(f"run-id={run or ''}")
    print(f"skip-rust={'true' if skip_rust else 'false'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
