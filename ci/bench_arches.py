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
`src/<module>.rs` or `src/hashes/<module>.rs` (for every architecture), or
`src/<family>/<hash>.rs`, whose module is `<family>_<hash>` (e.g.
`src/hmac/sha256.rs` is `hmac_sha256`, as in `src/asm/`). The
benchmarks decide which of them run (each lists the modules it `USES`, see
bench/benches/primitives/main.rs), and run everything for a module none of
them uses (e.g. `cpu`, `lib`, or `hashes/mod.rs`'s `mod`). Any other change
it benchmarks (e.g. the benchmarks themselves) runs every benchmark, and
`modules` is empty. The generated `src/asm/<arch>/mod.rs` only declares the
modules, so it narrows nothing either way.

An architecture with primitives that choose among implementations by CPU
feature is benchmarked once with every feature the runner has, and once
more for each restriction in `CPU_FEATURES` (as `VG_CPU_FEATURES`, see
src/cpu.rs), so that every implementation is measured. Each entry's
`cpu-features` is its restriction, empty for none.
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

# The other `VG_CPU_FEATURES` each architecture is benchmarked with.
CPU_FEATURES = {"x86_64": ["avx,avx2,bmi1,bmi2", "none"]}

SHARED = re.compile(
    r"src/|bench/|Cargo\.(toml|lock)$|ci/bench_(compare|arches)\.py$"
    r"|\.github/workflows/bench\.yml$"
)


# The file of one module: its assembly on one architecture, or its Rust API
# on every one.
ASM = re.compile(r"src/asm/([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
API = re.compile(r"src/(?:hashes/)?([a-z0-9_]+)\.rs$")
FAMILY = re.compile(r"src/(?!asm/|hashes/)([a-z0-9_]+)/([a-z0-9_]+)\.rs$")

ALL = None


def arches(changed):
    # The modules to benchmark on each architecture that needs it, or ALL.
    needed = {}

    def need(arch, module):
        if needed.get(arch, set()) is not ALL:
            needed.setdefault(arch, set()).add(module)

    for path in changed:
        asm, api, family = ASM.match(path), API.match(path), FAMILY.match(path)
        if asm and asm[1] in PLATFORMS:
            if asm[2] != "mod":
                need(asm[1], asm[2])
        elif api:
            for a in PLATFORMS:
                need(a, api[1])
        elif family:
            # A family's `mod.rs` names a module no benchmark uses, so
            # every benchmark runs.
            name = family[1] if family[2] == "mod" else f"{family[1]}_{family[2]}"
            for a in PLATFORMS:
                need(a, name)
        elif SHARED.match(path):
            for a in PLATFORMS:
                needed[a] = ALL
    return [p for a in PLATFORMS if a in needed for p in platforms(a, needed[a])]


def platforms(arch, modules=ALL):
    """The matrix entries of `arch`: one per CPU feature configuration."""
    return [
        {
            "arch": arch,
            **PLATFORMS[arch],
            "cpu-features": features,
            "modules": " ".join(sorted(modules or ())),
        }
        for features in ["", *CPU_FEATURES.get(arch, [])]
    ]


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        matrix = [p for a in PLATFORMS for p in platforms(a)]
    else:
        matrix = arches(sys.stdin.read().split())
    print(json.dumps(matrix))
