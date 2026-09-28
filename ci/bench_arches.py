"""Chooses which architectures' benchmarks a change needs.

    git diff --name-only BASE HEAD | python3 ci/bench_arches.py
    python3 ci/bench_arches.py --all

Prints a JSON list of platforms (see `PLATFORMS`) for the Benchmarks
workflow's matrix: an architecture is benchmarked when its own assembly
(`src/asm/<arch>/`) changed, or anything shared by every architecture (the
rest of `src/`, the benchmarks, the dependencies, the comparison). Changes
to other files (e.g. Lean that leaves `src/asm/` as it was) need none.
"""

import json
import re
import sys

# The architectures benchmarked, and where each one runs natively (as in
# ci.yml's `rust` job: the 32-bit ones in a 32-bit userspace container on
# the 64-bit host of the same family).
PLATFORMS = {
    "x86_64": {"os": "ubuntu-latest"},
    "aarch64": {"os": "ubuntu-24.04-arm"},
    "x86": {
        "os": "ubuntu-latest",
        "image": "rust:slim",
        "options": "--platform linux/386",
        "install-amd64-libc": True,
    },
    "arm": {
        "os": "ubuntu-24.04-arm",
        "image": "ghcr.io/pyca/cryptography-runner-ubuntu-rolling:armv7l",
        "options": "--env RUSTUP_HOME=/root/.rustup",
    },
}

SHARED = re.compile(
    r"src/|bench/|Cargo\.(toml|lock)$|ci/bench_(compare|arches)\.py$"
    r"|\.github/workflows/bench\.yml$"
)


def arches(changed):
    needed = set()
    for path in changed:
        arch = next((a for a in PLATFORMS if path.startswith(f"src/asm/{a}/")), None)
        if arch is not None:
            needed.add(arch)
        elif SHARED.match(path):
            needed.update(PLATFORMS)
    return [{"arch": a, **PLATFORMS[a]} for a in PLATFORMS if a in needed]


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        platforms = [{"arch": a, **PLATFORMS[a]} for a in PLATFORMS]
    else:
        platforms = arches(sys.stdin.read().split())
    print(json.dumps(platforms))
