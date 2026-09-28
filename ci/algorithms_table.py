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
  optimized  (optional) further Optimized entries that the code can't show,
           e.g. "ARM64 (NEON)" for tuning that needs no CPU feature

* Spec landed: every spec exists.
* Supported: the architectures in the `target_arch`s of every module's
  inner `#![cfg(...)]` (so every module must exist and have one).
* Optimized: the architectures where an `asm` module has functions that
  need CPU features (a generated `_FEATURES` constant), with the features,
  and then `optimized`.

`--check` writes nothing and fails if README.md is not up to date (CI runs
it).
"""

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
FAMILIES = ["Hashes", "MACs", "Ciphers", "AEADs", "KDFs"]

# How the table names CPU features (Rust's `target_feature` names); None
# leaves a feature out, e.g. one that only comes with another.
FEATURES = {
    "sha": "SHA extensions",
    "aes": "AES-NI",
    "pclmulqdq": "PCLMULQDQ",
    "ssse3": None,
}

CFG = re.compile(r"^#!\[cfg\((.*?)\)\]$", re.MULTILINE | re.DOTALL)
ARCH = re.compile(r'target_arch\s*=\s*"(\w+)"')
FEATURE_CONST = re.compile(r"_FEATURES: &\[&str\] = &\[(.*?)\];")


def arches(names):
    """A table cell for a set of architectures."""
    if not names:
        return "❌"
    if set(names) == set(ARCHES):
        return "✅"
    return ", ".join(ARCHES[a] for a in ARCHES if a in names)


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


def optimized(row, names):
    cells = []
    for arch in ARCHES:
        if arch not in names:
            continue
        features = []
        for asm in row["asm"]:
            path = ROOT / "src" / "asm" / arch / f"{asm}.rs"
            if path.is_file():
                for m in FEATURE_CONST.finditer(path.read_text()):
                    features += re.findall(r'"([^"]+)"', m[1])
        shown = []
        for f in features:
            f = FEATURES.get(f, f)
            if f is not None and f not in shown:
                shown.append(f)
        if shown:
            cells.append(f"{ARCHES[arch]} ({', '.join(shown)})")
    return ", ".join(cells + row.get("optimized", [])) or "❌"


def table(errors):
    header = "| Algorithm | Spec landed | Supported | Optimized |\n|---|---|---|---|\n"
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
        spec = all((ROOT / "lean/VerifiedGarbage/Spec" / f"{s}.lean").is_file() for s in row["specs"])
        names = supported(row, errors)
        families[row["family"]].append(
            f"| {row['name']} | {'✅' if spec else '❌'} | {arches(names)} | {optimized(row, names)} |\n"
        )
    return "\n".join(f"### {f}\n\n{header}{''.join(rows)}" for f, rows in families.items() if rows)


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
