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
other shared change (e.g. executable code in benchmarks' `main.rs`, or a benchmark whose
`USES` cannot be read) leaves `modules` empty, which runs every benchmark.

An architecture with primitives that choose among implementations by CPU
feature is benchmarked once with every feature the runner has, and once
more for each restriction in `CPU_FEATURES` (as `VG_CPU_FEATURES`, see
src/cpu.rs), so that every implementation is measured. Each entry's
`cpu-features` is its restriction, empty for none. With `--base REV`, edits
consisting only of module/benchmark registrations select their dependencies,
and code without feature variants or CPU dispatch needs one job per target.
Algorithms with variants keep the complete matrix, as do uncertain changes.
"""

import functools
import json
import pathlib
import subprocess
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


@functools.lru_cache(None)
def read(path, revision=None, root="."):
    if revision:
        result = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=root,
                                capture_output=True, text=True, check=False)
        return result.stdout if result.returncode == 0 else None
    try:
        return (pathlib.Path(root) / path).read_text()
    except FileNotFoundError:
        return None


def bench_uses(path, revision=None, root="."):
    text = read(path, revision, root)
    match = USES.search(text) if text is not None else None
    return set(re.findall(r'"([a-z0-9_]+)"', match[1])) if match else None


def bench_catalog(revision=None, root="."):
    main = read("bench/benches/primitives/main.rs", revision, root)
    names = set(re.findall(r"\(([a-z0-9_]+)::USES, \1::bench\)", main or ""))
    catalog = {name: bench_uses(f"bench/benches/primitives/{name}.rs", revision, root)
               for name in names}
    return catalog if catalog and all(catalog.values()) else None


def registrations(path, base):
    """Only changed module declarations/registry entries; other code means all."""
    if not base:
        return None
    diff = subprocess.check_output(["git", "diff", "--unified=0", base, "HEAD", "--", path], text=True)
    names = set()
    for line in diff.splitlines():
        if not line.startswith(("+", "-")) or line.startswith(("+++", "---")):
            continue
        line = line[1:].strip()
        if not line or line.startswith("//") or line == "#[rustfmt::skip]":
            continue
        match = re.fullmatch(r"(?:pub(?:\(crate\))? )?mod (\w+);|\((\w+)::USES, \2::bench\),", line)
        if not match:
            return None
        names.add(match[1] or match[2])
    return names


def scalar(arch, modules, base, catalogs):
    """Prune only feature-independent code; variants keep the original matrix.

    USES is the existing declaration of each benchmark's dependencies. Inspect
    both revisions, including dependencies removed from an existing benchmark.
    Unknown metadata and missing generated code retain the complete matrix.
    """
    if not base or modules is ALL or any(c is None for c in catalogs):
        return False
    names = {name for c in catalogs for name, uses in c.items() if uses & modules}
    uses = set().union(*(c.get(name, set()) for c in catalogs for name in names))
    found = False
    for revision in (base, None):
        for module in uses:
            text = read(f"src/asm/{arch}/{module}.rs", revision)
            found |= text is not None
            if text and "_FEATURES" in text:
                return False
            family, _, member = module.partition("_")
            for path in (f"src/{module}.rs", f"src/hashes/{module}.rs", f"src/{family}/{member}.rs"):
                api = read(path, revision) or ""
                if re.search(r"\bcpu\b|\b\w*Backend\w*\b|\bdetected\b|VG_CPU_FEATURES", api):
                    return False
    return found


def arches(changed, base=None):
    # The modules to benchmark on each architecture that needs it, or ALL.
    needed = {}
    catalogs = [bench_catalog(base), bench_catalog()]
    known = set().union(*catalogs[-1].values()) if catalogs[-1] else set()

    def need(arch, module):
        if module not in known:
            needed[arch] = ALL
        elif needed.get(arch, set()) is not ALL:
            needed.setdefault(arch, set()).add(module)

    for path in changed:
        asm, api, family = ASM.match(path), API.match(path), FAMILY.match(path)
        if path in ("src/lib.rs", "bench/benches/primitives/main.rs") or (asm and asm[2] == "mod"):
            names = registrations(path, base)
            for arch in ([asm[1]] if asm else PLATFORMS):
                if names is None:
                    needed[arch] = ALL
                for name in names or ():
                    if path.startswith("bench/"):
                        uses = set().union(*(c.get(name, set()) for c in catalogs if c))
                        if not uses:
                            needed[arch] = ALL
                        for module in uses:
                            need(arch, module)
                    else:
                        need(arch, name)
        elif asm and asm[1] in PLATFORMS:
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
    return [p for a in PLATFORMS if a in needed
            for p in platforms(a, needed[a], scalar(a, needed[a], base, catalogs))]


def platforms(arch, modules=ALL, scalar_only=False):
    """The matrix entries of `arch`: one per CPU feature configuration."""
    return [
        {
            "arch": arch,
            **PLATFORMS[arch],
            "cpu-features": features,
            "modules": " ".join(sorted(modules or ())),
        }
        for features in ([""] if scalar_only else ["", *CPU_FEATURES.get(arch, [])])
    ]


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        matrix = [p for a in PLATFORMS for p in platforms(a)]
    else:
        if sys.argv[1:] and (len(sys.argv) != 3 or sys.argv[1] != "--base"):
            sys.exit("usage: bench_arches.py [--all | --base REV]")
        matrix = arches(sys.stdin.read().split(), sys.argv[2] if len(sys.argv) == 3 else None)
    print(json.dumps(matrix))
