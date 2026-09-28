"""Chooses which architectures' benchmarks a change needs.

    git diff --name-only BASE HEAD | python3 ci/bench_arches.py
    python3 ci/bench_arches.py --all

Prints a JSON list of platforms (see `PLATFORMS`) for the Benchmarks
workflow's matrix: an architecture is benchmarked when its own assembly
(`src/asm/<arch>/`) changed, or anything shared by every architecture (the
rest of `src/`, the benchmarks, the dependencies, the comparison). Changes
to other files (e.g. Lean that leaves `src/asm/` as it was) need none.

Each platform's `modules` narrows its benchmarks to those of the modules
whose own files changed: `src/asm/<arch>/<module>.rs`, or the Rust API's
`src/<module>.rs` or `src/hashes/<module>.rs` (for every architecture). The
benchmarks decide which of them run (each lists the modules it `USES`, see
bench/benches/primitives/main.rs), and run everything for a module none of
them uses (e.g. `cpu`, `lib`, or `hashes/mod.rs`'s `mod`). Any other change
it benchmarks (e.g. the benchmarks themselves) runs every benchmark, and
`modules` is empty. The generated `src/asm/<arch>/mod.rs` only declares the
modules, so it narrows nothing either way.
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


# The file of one module: its assembly on one architecture, or its Rust API
# on every one.
ASM = re.compile(r"src/asm/([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
API = re.compile(r"src/(?:hashes/)?([a-z0-9_]+)\.rs$")

ALL = None


def arches(changed):
    # The modules to benchmark on each architecture that needs it, or ALL.
    needed = {}

    def need(arch, module):
        if needed.get(arch, set()) is not ALL:
            needed.setdefault(arch, set()).add(module)

    for path in changed:
        asm, api = ASM.match(path), API.match(path)
        if asm and asm[1] in PLATFORMS:
            if asm[2] != "mod":
                need(asm[1], asm[2])
        elif api:
            for a in PLATFORMS:
                need(a, api[1])
        elif SHARED.match(path):
            for a in PLATFORMS:
                needed[a] = ALL
    return [platform(a, needed[a]) for a in PLATFORMS if a in needed]


def platform(arch, modules=ALL):
    return {"arch": arch, **PLATFORMS[arch], "modules": " ".join(sorted(modules or ()))}


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        platforms = [platform(a) for a in PLATFORMS]
    else:
        platforms = arches(sys.stdin.read().split())
    print(json.dumps(platforms))
