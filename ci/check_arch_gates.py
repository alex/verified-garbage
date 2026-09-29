#!/usr/bin/env python3
"""Checks that every test and benchmark is built on exactly the
architectures whose library code it runs.

The architectures an algorithm supports are stated once, in the inner
`#![cfg(...)]` of its library module (`src/<module>.rs`, see CLAUDE.md);
a test or benchmark that repeats that list can drift from it, e.g. keep
benchmarking MD5 only on x86-64 after ARM64 support lands, or lose a
platform in a merge. So each test file (its inner `#![cfg(...)]`, within
those of the files that declare it) and each benchmark (the `#[cfg(...)]`
of its `pub fn bench`, and the `#[cfg(not(...))]` of the empty one for the
other architectures) must name exactly the architectures of the library
modules it uses (`verified_garbage::<path>`): all of them, where it uses
several. Where a construction over hash functions has a file per hash
(`src/<family>/<hash>.rs`, e.g. `src/hmac/sha256.rs`), a file that uses
both `<family>` and `hashes::<hash>` needs that file's architectures too.

Only `target_arch` is compared; other conditions (`feature = "alloc"`) are
allowed alongside.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ARCHES = frozenset({"x86_64", "aarch64", "arm", "x86"})

INNER_CFG = re.compile(r"^#!\[cfg\((.*?)\)\]$", re.MULTILINE | re.DOTALL)
BENCH_CFG = re.compile(r"^#\[cfg\(((?!not\().*?)\)\]\npub fn bench\(", re.MULTILINE | re.DOTALL)
NO_BENCH_CFG = re.compile(r"^#\[cfg\(not\((.*?)\)\)\]\npub fn bench\(", re.MULTILINE | re.DOTALL)
ARCH = re.compile(r'target_arch\s*=\s*"(\w+)"')
MOD_DECL = re.compile(r"^(?:pub(?:\(crate\))?\s+)?mod\s+(\w+);", re.MULTILINE)
USES = re.compile(r"verified_garbage::((?:\w+::)*\w+)")
USE_GROUP = re.compile(r"verified_garbage::(\w+)::\{([^}]*)\}", re.DOTALL)


def arch_set(cfg):
    """The architectures a cfg predicate allows: those it names, or all of
    them if it names none."""
    names = set(ARCH.findall(cfg))
    return frozenset(names) if names else ARCHES


def inner(path):
    m = INNER_CFG.search(path.read_text())
    return arch_set(m[1]) if m else ARCHES


def library():
    """The architectures of each library module, by its path under the
    crate (e.g. `hashes::md5`), within those of its parents."""
    mods = {}

    def walk(path, name, parent):
        archs = parent & inner(path)
        if name:
            mods[name] = archs
        folder = path.parent if path.name in ("lib.rs", "mod.rs") else path.with_suffix("")
        for child in MOD_DECL.findall(path.read_text()):
            if child in ("asm", "cpu", "tests"):
                continue
            for sub in (folder / f"{child}.rs", folder / child / "mod.rs"):
                if sub.is_file():
                    walk(sub, f"{name}::{child}" if name else child, archs)

    walk(ROOT / "src" / "lib.rs", "", ARCHES)
    return mods


def required(text, mods):
    """The architectures of every library module `text` uses."""
    paths = set(USES.findall(text))
    for family, items in USE_GROUP.findall(text):
        for item in items.split(","):
            item = item.strip().split(" as ")[0].strip()
            if item and item != "self":
                paths.add(f"{family}::{item}")
    used = set()
    for p in paths:
        parts = p.split("::")
        for n in range(len(parts), 0, -1):
            if "::".join(parts[:n]) in mods:
                used.add("::".join(parts[:n]))
                break
    archs = ARCHES
    for u in used:
        archs &= mods[u]
    hashes = {u.split("::")[1] for u in used if u.startswith("hashes::") and u.count("::") == 1}
    for u in used:
        for h in hashes:
            per_hash = f"{u}::{h}"
            if "::" not in u and per_hash in mods:
                archs &= mods[per_hash]
    return archs, used


def declared_in(path):
    """The files that declare `path` as a module, from its crate root down
    (tests/<crate>/main.rs, then any mod.rs in between)."""
    chain = []
    parent = path.parent
    while parent != ROOT / "tests" and parent != ROOT / "bench" / "benches":
        for root in ("main.rs", "mod.rs"):
            f = parent / root
            if f.is_file() and f != path:
                chain.append(f)
        parent = parent.parent
    return chain


def show(archs):
    return ", ".join(sorted(archs))


def main() -> int:
    mods = library()
    errors = []
    for path in sorted((ROOT / "tests").rglob("*.rs")):
        text = path.read_text()
        archs, used = required(text, mods)
        if not used:
            continue
        gate = inner(path)
        for f in declared_in(path):
            gate &= inner(f)
        if gate != archs:
            errors.append(
                f"{path.relative_to(ROOT)}: built for {show(gate)}, but what it uses "
                f"({', '.join(sorted(used))}) is on {show(archs)}"
            )
    for path in sorted((ROOT / "bench" / "benches").rglob("*.rs")):
        text = path.read_text()
        archs, used = required(text, mods)
        if "pub fn bench(" not in text or not used:
            continue
        m = BENCH_CFG.search(text)
        gate = arch_set(m[1]) if m else ARCHES
        empty = NO_BENCH_CFG.search(text)
        if empty and arch_set(empty[1]) != gate:
            errors.append(
                f"{path.relative_to(ROOT)}: the empty `bench` is not for exactly the other "
                "architectures"
            )
        if gate != archs:
            errors.append(
                f"{path.relative_to(ROOT)}: `bench` runs on {show(gate)}, but what it uses "
                f"({', '.join(sorted(used))}) is on {show(archs)}"
            )
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        print("gate each on exactly the architectures of the library code it runs", file=sys.stderr)
        return 1
    print("test and benchmark architecture gates OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
