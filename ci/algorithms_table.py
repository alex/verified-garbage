#!/usr/bin/env python3
"""Generates the table in the Algorithms section of README.md.

The table is built from what the repository contains, so that no PR edits
it by hand (and two PRs for the same algorithm never conflict over a row):
rerun this script instead. Each docs/algorithms/<name>.toml is a row:

  name     what the table calls it
  family   the table it goes in, one of FAMILIES
  specs    its Lean specs, lean/VerifiedGarbage/Spec/<spec>.lean
  modules  the Rust modules of its public API
  asm      the generated modules, src/asm/<arch>/<asm>.rs, whose functions
           it runs
  optimized  (optional) notes on optimizations that the code can't show, by
           Rust architecture name, e.g. { aarch64 = "NEON" } for tuning
           that needs no CPU feature

* Spec landed: every spec exists.
* One column per architecture: ✅ if it is in the `target_arch`s of every
  module's inner `#![cfg(...)]` (so every module must exist and have one),
  followed by the CPU features that its `asm` modules' functions need (a
  generated `_FEATURES` constant) and its `optimized` note, if any.

The table is HTML with every cell on a line of its own, between blank
lines, so that git merges two PRs that change different cells (say, two
architectures of one algorithm) without a conflict.

`--check` writes nothing and fails if README.md is not up to date (CI runs
it).
"""

import html
import pathlib
import re
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent
README = ROOT / "README.md"
ROWS = ROOT / "docs" / "algorithms"
BEGIN = "<!-- BEGIN ci/algorithms_table.py: edit docs/algorithms/, then run it -->\n"
END = "<!-- END ci/algorithms_table.py -->\n"

# The architectures, in table order: Rust's name and the table's.
ARCHES = {"x86_64": "x86-64", "aarch64": "ARM64", "arm": "ARMv7", "x86": "x86"}

# The families, in README order: each has its own table, under a heading.
FAMILIES = ["Hashes", "MACs", "Ciphers", "AEADs", "KDFs", "KEMs", "Key agreement", "Signatures"]

# How the table names CPU features (Rust's `target_feature` names), in the
# order it lists them; None leaves a feature out, e.g. one that only comes
# with another.
FEATURES = {
    "sha": "SHA extensions",
    "sha512": "SHA512",
    "aes": "AES-NI",
    "pclmulqdq": "PCLMULQDQ",
    "ssse3": None,
    "avx512f": "AVX-512F",
    "avx2": "AVX2",
    "avx": None,
    "bmi1": "BMI1",
    "bmi2": "BMI2",
    "adx": "ADX",
}

# Names that differ on one architecture: AArch64's `aes` (Rust's name for
# FEAT_AES with FEAT_PMULL) is not AES-NI.
ARCH_FEATURES = {"aarch64": {"aes": "AES, PMULL", "sha2": "SHA extensions", "sha3": "SHA extensions"}}

CFG = re.compile(r"^#!\[cfg\((.*?)\)\]$", re.MULTILINE | re.DOTALL)
ARCH = re.compile(r'target_arch\s*=\s*"(\w+)"')
FEATURE_CONST = re.compile(r"_FEATURES: &\[&str\] = &\[(.*?)\];")


def supported(row, errors):
    names = set(ARCHES)
    for module in row["modules"]:
        path = ROOT / module
        if not path.is_file():
            return set()
        cfg = CFG.search(path.read_text())
        if not cfg:
            errors.append(f"{module}: no inner #![cfg(...)] naming its architectures")
            return set()
        names &= set(ARCH.findall(cfg[1]))
    return names


def optimized(row, arch):
    """The CPU features and notes of `row`'s optimizations on `arch`."""
    features = []
    for asm in row["asm"]:
        path = ROOT / "src" / "asm" / arch / f"{asm}.rs"
        if path.is_file():
            for m in FEATURE_CONST.finditer(path.read_text()):
                features += re.findall(r'"([^"]+)"', m[1])
    order = list(FEATURES)
    shown = []
    for f in sorted(set(features), key=lambda f: (order.index(f) if f in order else len(order), f)):
        f = {**FEATURES, **ARCH_FEATURES.get(arch, {})}.get(f, f)
        if f is not None:
            shown.append(f)
    note = row.get("optimized", {}).get(arch)
    return ", ".join(shown) + ("; " if shown and note else "") + (note or "")


def cell(text):
    """A cell's HTML: `code` spans become <code>, the rest is escaped."""
    parts = html.escape(text, quote=False).split("`")
    return "".join(f"<code>{p}</code>" if i % 2 else p for i, p in enumerate(parts))


def tr(tag, cells):
    """A table row, with every cell on its own line between blank lines."""
    return "<tr>\n\n" + "".join(f"<{tag}>{c}</{tag}>\n\n" for c in cells) + "</tr>\n\n"


def table(errors):
    header = tr("th", ["Algorithm", "Spec landed", *ARCHES.values()])
    families = {f: [] for f in FAMILIES}
    for path in sorted(ROWS.glob("*.toml")):
        row = tomllib.loads(path.read_text())
        missing = [k for k in ("name", "family", "specs", "modules", "asm") if k not in row]
        if missing:
            errors.append(f"{path.relative_to(ROOT)}: missing {', '.join(missing)}")
            continue
        if row["family"] not in families:
            errors.append(f"{path.relative_to(ROOT)}: family must be one of {', '.join(FAMILIES)}")
            continue
        unknown = set(row.get("optimized", {})) - set(ARCHES)
        if unknown:
            errors.append(f"{path.relative_to(ROOT)}: optimized names unknown architectures {sorted(unknown)}")
            continue
        spec = all((ROOT / "lean/VerifiedGarbage/Spec" / f"{s}.lean").is_file() for s in row["specs"])
        names = supported(row, errors)
        cells = [row["name"], "✅" if spec else "❌"]
        for arch in ARCHES:
            opt = optimized(row, arch) if arch in names else ""
            cells.append(("✅" if arch in names else "❌") + (f" {opt}" if opt else ""))
        families[row["family"]].append(tr("td", [cell(c) for c in cells]))
    return "\n".join(
        f"### {f}\n\n<table>\n\n{header}{''.join(rows)}</table>\n" for f, rows in families.items() if rows
    )


def main() -> int:
    check = sys.argv[1:] == ["--check"]
    errors = []
    text = README.read_text()
    if BEGIN not in text or END not in text:
        errors.append(f"README.md: no {BEGIN.strip()} ... {END.strip()} section")
    else:
        head, rest = text.split(BEGIN, 1)
        _, tail = rest.split(END, 1)
        new = head + BEGIN + "\n" + table(errors) + "\n" + END + tail
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    if new == text:
        print("README.md algorithm table OK")
        return 0
    if check:
        print("README.md's algorithm table is out of date: run python3 ci/algorithms_table.py", file=sys.stderr)
        return 1
    README.write_text(new)
    print("wrote README.md")
    return 0


if __name__ == "__main__":
    sys.exit(main())
