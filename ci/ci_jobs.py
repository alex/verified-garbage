"""Chooses which of CI's slow jobs a change needs.

    git diff --name-only BASE HEAD | python3 ci/ci_jobs.py
    python3 ci/ci_jobs.py --all

Prints `lean=true|false` and `rust=true|false`, for `$GITHUB_OUTPUT`.

A job is skipped only when every changed file is one it is known not to
read; any other file (including one added under a new path) runs it. So
the lists below say what each job can ignore, never what it needs:

* The Lean job reads `lean/`, and checks `src/asm/` against it.
* The Rust jobs (and coverage, which merges theirs) read everything else
  but the Lean sources, prose, the benchmarks (a separate crate, with its
  own workflow) and the scripts of other jobs.

Both run when ci.yml or this script changes, since they define the jobs.
"""

import re
import sys

# The definitions of the jobs, and of this choice.
ALWAYS = {".github/workflows/ci.yml", "ci/ci_jobs.py"}

LEAN_IGNORES = re.compile(r"(?!lean/|src/asm/)")

RUST_IGNORES = re.compile(
    r"lean/"
    r"|(?!src/|tests/)[^/]+(/[^/]+)*\.md$"
    r"|LICENSE[^/]*$"
    r"|bench/"
    r"|ci/(bench_[a-z]+|check_lean_[a-z]+|check_vectors)\.py$"
    r"|\.github/(workflows/bench\.yml|dependabot\.yml)$"
)


def needs(changed, ignores):
    return any(path in ALWAYS or not ignores.match(path) for path in changed)


def main():
    if sys.argv[1:] == ["--all"]:
        changed = list(ALWAYS)
    else:
        changed = [line for line in sys.stdin.read().splitlines() if line]
    for job, ignores in (("lean", LEAN_IGNORES), ("rust", RUST_IGNORES)):
        print(f"{job}={str(needs(changed, ignores)).lower()}")


if __name__ == "__main__":
    main()
