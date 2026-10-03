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
  * `src/<family>/<hash>.rs`: `<family>_<hash>` (as in `src/asm/`), and
    `src/<family>/mod.rs`: every `<family>_<hash>`;
  * `bench/benches/primitives/<name>.rs`, or its differential test
    `bench/tests/<name>.rs`: the modules in its `USES`.

The benchmarks run those that use any of them, and all of them for a module
none uses (e.g. `lib`, or the generated `src/asm/<arch>/mod.rs`). Any
other shared change (e.g. executable code in benchmarks' `main.rs`, or a benchmark whose
`USES` cannot be read) leaves `modules` empty, which runs every benchmark.

A change to `src/cpu.rs` needs, on each architecture, the modules that
choose among implementations by a feature whose detection changed there:
the first feature each changed line names (the one it detects, as in
`let vaes = (ecx7 >> 9) & avx;`), in an item only one architecture (or a
few) compiles, such as its `runtime()`, or all its features if those lines
name none. A change to an item every architecture compiles (`Features`,
`detected()`) needs every module that chooses by a feature, on the
architectures detecting any; one to its tests, its comments or the names
appended to `NAMES` needs nothing. Its other code (choosing an
implementation once, when an object is created) is the same everywhere, so
measuring it where something is chosen suffices.

An architecture with primitives that choose among implementations by CPU
feature is benchmarked once with every feature the runner has, and once
more for each restriction in `CPU_FEATURES` (as `VG_CPU_FEATURES`, see
src/cpu.rs), so that every implementation is measured. Each entry's
`cpu-features` is its restriction, empty for none. With `--base REV`, edits
consisting only of module/benchmark registrations select their dependencies.

When only some benchmarks run, a configuration runs only if it can choose
other implementations of them than the configurations before it: one that
allows the same of the feature sets they choose by is left out. A benchmark
chooses by the features of each of its `USES` modules' generated variants
(a `_FEATURES` constant of `src/asm/<arch>/<module>.rs`) and by each feature
its architecture detects that their Rust code names in quotes (e.g.
`chacha20`'s `"neon"`), at base and at head. A module whose Rust code reads `VG_CPU_FEATURES` itself (on
AArch64, SHA-3 uses FEAT_SHA3 only when it is named) depends on which of its
features each configuration names. All benchmarks run every configuration.
"""

import difflib
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
# Ed25519's combinations of SHA-512 and field multiplication, and, on
# x86-64 and x86, AES-GCM's `_aesni` and `_pclmul`, which a runner with
# both extensions never chooses; on AArch64, ChaCha20's `_neon` instances,
# which the SVE2 runner never chooses; no runner has the SHA512 extension,
# whose variants only ci.yml tests, under SDE).
CPU_FEATURES = {
    "x86_64": [
        "avx,avx2,bmi1,bmi2,adx",
        "avx,avx2,bmi1,bmi2",
        "bmi2,adx",
        "avx,avx2,bmi2,adx,avx512ifma,avx512vl",
        "aes,ssse3",
        "pclmulqdq,ssse3",
        "none",
    ],
    "aarch64": ["neon", "sha3", "none"],
    "x86": ["aes", "pclmulqdq,ssse3", "none"],
}

# Changes to this script choose benchmarks but are not measured by any:
# `ci/test_check_benchmarks.py` tests it.
SHARED = re.compile(
    r"src/|bench/|Cargo\.(toml|lock)$|ci/bench_compare\.py$"
    r"|\.github/workflows/bench\.yml$"
)


# The file of one module: its assembly on one architecture, or its Rust API
# on every one.
ASM = re.compile(r"src/asm/([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
API = re.compile(r"src/(?:hashes/)?([a-z0-9_]+)\.rs$")
FAMILY = re.compile(r"src/(?!asm/|hashes/)([a-z0-9_]+)/([a-z0-9_]+)\.rs$")
# One algorithm's benchmark, and the modules it lists in its `USES`.
BENCH = re.compile(r"bench/benches/primitives/(?!main\.rs$)([a-z0-9_]+)\.rs$")
# A differential test of one algorithm's benchmark's API, next to it.
BENCH_TEST = re.compile(r"bench/tests/([a-z0-9_]+)\.rs$")
USES = re.compile(r"pub const USES: &\[&str\] = &\[([^\]]*)\];")
QUOTED = re.compile(r'"([a-z0-9_]+)"')
# A generated variant's CPU features, and the features `src/cpu.rs` knows.
FEATURES = re.compile(r"_FEATURES: &\[&str\] = &\[([^\]]*)\];")
NAMES = re.compile(r"const NAMES: \[&str; \d+\] = \[([^\]]*)\];")
# Each architecture's feature detection in `src/cpu.rs`: its `cfg`, and the
# body, which names each feature in quotes or as a `let`.
RUNTIME = re.compile(r"(#\[cfg\([^\n]*\)\])\nfn runtime\(\) -> u32 \{\n(.*?)\n\}\n", re.S)
LET = re.compile(r"\blet ([a-z0-9_]+) =")
# Code choosing by what `VG_CPU_FEATURES` names, not only by what it allows.
OPT_IN = re.compile(r'var\("VG_CPU_FEATURES"\)')

# The first line of an item of `src/cpu.rs`: in column 0, and not a
# comment, an attribute or the end of an item.
ITEM_START = re.compile(r"(?!//|#\[|[\s})\]]|$)")

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


def members(family, known):
    """The modules of a family: `<family>_<hash>`."""
    return {m for m in known if m.startswith(f"{family}_")}


def rust_files(root="."):
    return sorted(p.relative_to(root).as_posix() for p in pathlib.Path(root, "src").glob("**/*.rs"))


def users(family, known, root="."):
    """The modules whose Rust code (outside the family's) uses the family's
    shared code; a file that is no module's names itself, which no
    benchmark uses."""
    names = set()
    for path in rust_files(root):
        if path.startswith(("src/asm/", f"src/{family}/")) or not re.search(
                rf"\bcrate::{family}::", read(path, None, root) or ""):
            continue
        api, other = API.match(path), FAMILY.match(path)
        if api:
            names.add(api[1])
        elif other and other[2] == "mod":
            names |= members(other[1], known) or {path}
        else:
            names.add(f"{other[1]}_{other[2]}" if other else path)
    return names


def sources(module):
    """The Rust files that can choose among `module`'s implementations."""
    paths = [f"src/{module}.rs", f"src/{module}/mod.rs", f"src/hashes/{module}.rs", "src/hashes/mod.rs"]
    family, _, hash_ = module.partition("_")
    if hash_:
        paths += [f"src/{family}/{hash_}.rs", f"src/{family}/mod.rs"]
    return paths


def detectable(arch, cpu):
    """The features `src/cpu.rs` (the text `cpu`) can detect on `arch`, from
    its `runtime()` for that architecture, or None if there is none."""
    names = NAMES.search(cpu)
    if not names:
        return None
    known = set(QUOTED.findall(names[1]))
    found = None
    for cfg, body in RUNTIME.findall(cpu):
        if arch in re.findall(r'target_arch = "([a-z0-9_]+)"', cfg):
            found = (found or set()) | (set(QUOTED.findall(body)) | set(LET.findall(body))) & known
    return found


def requirements(arch, modules, revisions):
    """The sets of CPU features that choose among `modules`' implementations
    on `arch`, at any of `revisions`: each variant's, and each feature named
    in their Rust code alone; with `<name>!` for a feature that chooses only
    when `VG_CPU_FEATURES` names it. None if the features `arch` can detect
    cannot be read."""
    reqs = set()
    for revision in revisions:
        arch_features = detectable(arch, read("src/cpu.rs", revision) or "")
        if arch_features is None:
            return None if CPU_FEATURES.get(arch) else set()
        quoted = re.compile(r'"(%s)"' % "|".join(map(re.escape, sorted(arch_features))))
        for module in modules:
            asm = read(f"src/asm/{arch}/{module}.rs", revision) or ""
            found = {frozenset(QUOTED.findall(lst)) for lst in FEATURES.findall(asm)}
            opt_in = False
            for path in sources(module):
                text = read(path, revision) or ""
                if arch_features:
                    found |= {frozenset([name]) for name in quoted.findall(text)}
                opt_in |= bool(OPT_IN.search(text))
            found = {req for req in found if req and req <= arch_features}
            reqs |= {req | {f"{name}!" for name in req} for req in found} if opt_in else found
    return reqs


def allows(restriction, reqs):
    """Which of `reqs` a `VG_CPU_FEATURES` of `restriction` allows (on a CPU
    with every feature)."""
    named = set() if restriction in ("", "none") else set(restriction.split(","))

    def allowed(feature):
        if feature.endswith("!"):
            return feature[:-1] in named
        return not restriction or feature in named
    return frozenset(req for req in reqs if all(map(allowed, req)))


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
        elif path == "src/cpu.rs":
            changes = cpu_changes(base)
            for a in PLATFORMS:
                if changes is None:
                    needed[a] = ALL
                    continue
                if "*" not in changes and a not in changes:
                    continue
                modules = cpu_modules(a, ALL if "*" in changes else changes[a], known,
                                      [base, None] if base else [None])
                if modules is None:
                    needed[a] = ALL
                for module in modules or ():
                    need(a, module)
        elif asm and asm[1] in PLATFORMS:
            need(asm[1], asm[2])
        elif api:
            for a in PLATFORMS:
                need(a, api[1])
        elif family:
            # A family's `mod.rs` is the code its `<family>_<hash>` modules
            # share, which others may use too; with no module, every
            # benchmark runs.
            names = ((members(family[1], known) | users(family[1], known)) or {family[1]}
                     if family[2] == "mod" else {f"{family[1]}_{family[2]}"})
            for a in PLATFORMS:
                for name in names:
                    need(a, name)
        elif (bench := BENCH.match(path) or BENCH_TEST.match(path)) and (
                uses := bench_uses(f"bench/benches/primitives/{bench[1]}.rs")):
            for a in PLATFORMS:
                for m in uses:
                    need(a, m)
        elif SHARED.match(path):
            for a in PLATFORMS:
                needed[a] = ALL
    revisions = [base, None] if base else [None]
    return [p for a in PLATFORMS if a in needed
            for p in platforms(a, needed[a], run_requirements(a, needed[a], catalogs, revisions))]


def cpu_item(lines, i):
    """The item of `src/cpu.rs` (as `lines`) line `i` is in: its first line,
    and its attributes."""
    while i < len(lines) - 1 and lines[i].startswith("#["):  # The next item's.
        i += 1
    while i > 0 and not ITEM_START.match(lines[i]):
        i -= 1
    attributes = []
    j = i - 1
    while j >= 0 and lines[j].startswith(("#[", "///")):
        attributes += [lines[j]] if lines[j].startswith("#[") else []
        j -= 1
    return lines[i], attributes


def cpu_changes(base):
    """What the change to `src/cpu.rs` since `base` affects: for each
    architecture whose own detection changed, the first feature each changed
    line names (ALL if none does); "*" for a change to code every
    architecture compiles; None if either revision cannot be read."""
    old, new = read("src/cpu.rs", base) if base else None, read("src/cpu.rs")
    if old is None or new is None:
        return None
    names = [QUOTED.findall(m[1]) if (m := NAMES.search(t)) else [] for t in (old, new)]
    known = set(names[0]) | set(names[1])
    sides = [old.splitlines(), new.splitlines()]
    items = {}
    matcher = difflib.SequenceMatcher(None, *sides, autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == "equal":
            continue
        for side, lo, hi in ((0, i1, i2), (1, j1, j2)):
            for k in range(lo, hi):
                code = sides[side][k].split("//")[0].strip()
                if not code:
                    continue
                first, attributes = cpu_item(sides[side], k)
                cfgs = [a for a in attributes if a.startswith("#[cfg(")]
                if "#[cfg(test)]" in cfgs:
                    continue
                if re.search(r"\bconst NAMES\b", first):
                    # Names appended change no other feature's bit, and
                    # choose nothing until something detects them.
                    a, b = names
                    if a == b[:len(a)] or b == a[:len(b)]:
                        continue
                    arches = "*"
                else:
                    arches = frozenset(re.findall(r'target_arch = "([a-z0-9_]+)"', " ".join(cfgs)))
                    if not arches or any("not(" in c for c in cfgs):
                        arches = "*"
                key = (arches, first.strip())
                # The feature a line detects comes first (`let vaes = … & avx`).
                named = [n for n in re.findall(r"[a-z0-9_]+", code) if n in known]
                items.setdefault(key, set()).update(named[:1])
    changes = {}
    for (arches, _), features in items.items():
        for arch in [arches] if arches == "*" else arches:
            if not features or arches == "*":
                changes[arch] = ALL
            elif changes.get(arch, set()) is not ALL:
                changes.setdefault(arch, set()).update(features)
    return changes


def cpu_modules(arch, changes, known, revisions):
    """The modules `known` on `arch` that choose by a feature in `changes`
    (ALL: by any), or None if what they choose by cannot be read."""
    modules = set()
    for module in sorted(known):
        reqs = requirements(arch, {module}, revisions)
        if reqs is None:
            return None
        if any(changes is ALL or {f.rstrip("!") for f in req} & changes for req in reqs):
            modules.add(module)
    return modules


def run_requirements(arch, modules, catalogs, revisions):
    """The `requirements` of the benchmarks that use any of `modules`, or
    None (every configuration) for all of them or an unreadable catalog."""
    if modules is ALL or not all(catalogs):
        return None
    uses = {m for c in catalogs for u in c.values() if u & modules for m in u}
    return requirements(arch, uses, revisions)


def platforms(arch, modules=ALL, reqs=None):
    """The matrix entries of `arch`: one per CPU feature configuration, but
    with `reqs`, only the first of those allowing the same of them."""
    configurations = ["", *CPU_FEATURES.get(arch, [])]
    if reqs is not None:
        chosen = {}
        for features in configurations:
            allowed = allows(features, reqs)
            # One allowing none of them is the one that names none.
            if allowed not in chosen or (features == "none" and chosen[allowed]):
                chosen[allowed] = features
        configurations = [f for f in configurations if f in chosen.values()]
    return [
        {
            "arch": arch,
            **PLATFORMS[arch],
            "cpu-features": features,
            "modules": " ".join(sorted(modules or ())),
        }
        for features in configurations
    ]


if __name__ == "__main__":
    if sys.argv[1:] == ["--all"]:
        matrix = [p for a in PLATFORMS for p in platforms(a)]
    else:
        if sys.argv[1:] and (len(sys.argv) != 3 or sys.argv[1] != "--base"):
            sys.exit("usage: bench_arches.py [--all | --base REV]")
        matrix = arches(sys.stdin.read().split(), sys.argv[2] if len(sys.argv) == 3 else None)
    print(json.dumps(matrix))
