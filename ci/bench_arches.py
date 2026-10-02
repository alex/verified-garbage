"""Chooses which architectures' benchmarks a change needs.

    git diff --name-only BASE HEAD | python3 ci/bench_arches.py
    python3 ci/bench_arches.py --all

Prints a JSON list of platforms (see `PLATFORMS`) for the Benchmarks
workflow's matrix: an architecture is benchmarked when its own assembly
(`src/asm/<arch>/`) changed, or anything shared by every architecture (the
rest of `src/`, the benchmarks, the dependencies, the comparison). Changes
to other files (e.g. Lean that leaves `src/asm/` as it was) need none.

Each platform's `modules` narrows its benchmarks to the modules whose own
files changed:

  * `src/asm/<arch>/<module>.rs`: `<module>`, on that architecture;
  * `src/<module>.rs` or `src/hashes/<module>.rs`: `<module>`;
  * `src/<family>/<hash>.rs`: `<family>_<hash>` (as in `src/asm/`);
  * `bench/benches/primitives/<name>.rs`: the modules in its `USES`.

The benchmarks run those that use any of them, and all of them for a module
none uses (e.g. `cpu`, `lib`, or the generated `src/asm/<arch>/mod.rs`). Any
other shared change (e.g. the benchmarks' `main.rs`, or a benchmark whose
`USES` cannot be read) leaves `modules` empty, which runs every benchmark.

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
        "options": "--env RUSTUP_HOME=/tmp/verified-garbage-rustup",
    },
}

# The other `VG_CPU_FEATURES` each architecture is benchmarked with, so that
# each implementation a runner can run is measured (on x86-64, each of
# Ed25519's combinations of SHA-512 and field multiplication; no runner has
# the SHA512 extension, whose variants only ci.yml tests, under SDE).
CPU_FEATURES = {
    "x86_64": [
        "avx,avx2,bmi1,bmi2,adx",
        "avx,avx2,bmi1,bmi2",
        "bmi2,adx",
        "avx,avx2,bmi2,adx,avx512ifma,avx512vl",
        "none",
    ],
    "aarch64": ["sha3", "none"],
    "x86": ["none"],
}

SHARED = re.compile(
    r"src/|bench/|Cargo\.(toml|lock)$|ci/bench_(compare|arches)\.py$"
    r"|\.github/workflows/bench\.yml$"
)


# The file of one module: its assembly on one architecture, or its Rust API
# on every one.
ASM = re.compile(r"src/asm/([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
API = re.compile(r"src/(?:hashes/)?([a-z0-9_]+)\.rs$")
FAMILY = re.compile(r"src/(?!asm/|hashes/)([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
# One algorithm's benchmark, and the modules it lists in its `USES`.
BENCH = re.compile(r"bench/benches/primitives/(?!main\.rs$)[a-z0-9_]+\.rs$")
USES = re.compile(r"pub const USES: &\[&str\] = &\[([^\]]*)\];")

ALL = None


def bench_uses(path):
    """The modules the benchmark at `path` lists in its `USES`, or None if
    it cannot be read (e.g. a deleted benchmark) or lists none."""
    try:
        with open(path) as f:
            m = USES.search(f.read())
    except OSError:
        return None
    modules = re.findall(r'"([a-z0-9_]+)"', m[1]) if m else []
    return modules or None


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
        elif BENCH.match(path) and (uses := bench_uses(path)):
            for a in PLATFORMS:
                for m in uses:
                    need(a, m)
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
