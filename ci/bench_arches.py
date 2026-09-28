"""Chooses which architectures' benchmarks a change needs, and which
benchmarks.

    git diff --name-only BASE HEAD | python3 ci/bench_arches.py
    python3 ci/bench_arches.py --all
    git diff --name-only BASE HEAD | python3 ci/bench_arches.py --benchmarks

Prints a JSON list of platforms (see `PLATFORMS`) for the Benchmarks
workflow's matrix: an architecture is benchmarked when its own assembly
(`src/asm/<arch>/`) changed, or anything shared by every architecture (the
rest of `src/`, the benchmarks, the dependencies, the comparison). Changes
to other files (e.g. Lean that leaves `src/asm/` as it was) need none.

With `--benchmarks`, prints the benchmark groups for
`ci/bench_compare.py --benchmarks`: those of the algorithms whose code
changed (see `BENCHMARKS`), or nothing to run them all, when no
algorithm's code changed or: a change to anything else in `src/` (e.g. `lib.rs`,
`cpu.rs`, a `mod.rs`), to the benchmarks themselves or to the comparison
may affect them all.
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


# The benchmark groups (the `<primitive>` of each id) of each module of
# `src/`, by file stem: its Rust API (`src/<module>.rs`,
# `src/hashes/<module>.rs`) and its assembly (`src/asm/<arch>/<module>.rs`).
BENCHMARKS = {
    "chacha20": ["chacha20"],
    "md5": ["md5"],
    "sha1": ["sha1"],
    # HMAC-SHA256 hashes with SHA-256.
    "sha256": ["sha256", "sha256-baseline", "hmac-sha256", "hmac-sha256-baseline"],
    "sha512": ["sha512"],
    "sha3": ["sha3-224", "sha3-256", "sha3-384", "sha3-512", "shake128", "shake256"],
    "hmac": ["hmac-sha256", "hmac-sha256-baseline"],
    "aes_gcm": ["aes-128-gcm-encrypt", "aes-128-gcm-decrypt", "aes-128-gcm-stream"],
    "aes": ["aes-128-gcm-encrypt", "aes-128-gcm-decrypt", "aes-128-gcm-stream"],
    "gcm": ["aes-128-gcm-encrypt", "aes-128-gcm-decrypt", "aes-128-gcm-stream"],
    # Only run by the library's own tests.
    "selftest": [],
}

MODULE = re.compile(r"src/(?:hashes/|asm/[^/]+/)?([^/]+)\.rs$")


def benchmarks(changed):
    """The groups the changes need, or None (or none) for all of them."""
    needed = set()
    for path in changed:
        module = MODULE.match(path)
        if module and module[1] in BENCHMARKS:
            needed.update(BENCHMARKS[module[1]])
        elif SHARED.match(path):
            return None
    return sorted(needed)


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
    if sys.argv[1:] == ["--benchmarks"]:
        print("|".join(benchmarks(sys.stdin.read().split()) or []))
    else:
        if sys.argv[1:] == ["--all"]:
            platforms = [{"arch": a, **PLATFORMS[a]} for a in PLATFORMS]
        else:
            platforms = arches(sys.stdin.read().split())
        print(json.dumps(platforms))
