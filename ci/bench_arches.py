"""Chooses which architectures' benchmarks a change needs.

    git diff --name-only BASE HEAD | python3 ci/bench_arches.py

Prints a JSON list of `{"arch": ..., "os": ...}` for the Benchmarks
workflow's matrix: an architecture is benchmarked when its own assembly
(`src/asm/<arch>/`) changed, or anything shared by every architecture (the
rest of `src/`, the benchmarks, the dependencies, the comparison). Changes
to other files (e.g. Lean that leaves `src/asm/` as it was) need none.
"""

import json
import re
import sys

# The architectures benchmarked, and the runner each one runs on natively.
RUNNERS = {"x86_64": "ubuntu-latest", "aarch64": "ubuntu-24.04-arm"}

# The directories of `src/asm/` that only one architecture uses.
ARCH_DIRS = ("x86_64", "aarch64", "x86", "arm")

SHARED = re.compile(
    r"src/|bench/|Cargo\.(toml|lock)$|ci/bench_(compare|arches)\.py$"
    r"|\.github/workflows/bench\.yml$"
)


def arches(changed):
    needed = set()
    for path in changed:
        arch_dir = next((a for a in ARCH_DIRS if path.startswith(f"src/asm/{a}/")), None)
        if arch_dir is not None:
            if arch_dir in RUNNERS:
                needed.add(arch_dir)
        elif SHARED.match(path):
            needed.update(RUNNERS)
    return [{"arch": a, "os": RUNNERS[a]} for a in RUNNERS if a in needed]


if __name__ == "__main__":
    print(json.dumps(arches(sys.stdin.read().split())))
