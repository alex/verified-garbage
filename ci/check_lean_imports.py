#!/usr/bin/env python3
"""Checks the import discipline between the directories of
lean/VerifiedGarbage/, which keeps the trusted base small and separate from
proofs. Exits non-zero on violations.

  * TCB/   imports only Lean core and TCB/  (no Mathlib: smaller trusted base).
  * Spec/  imports only TCB/, Spec/ and Mathlib.
  * Impl/  imports only TCB/, Spec/, Impl/ and Mathlib (never proofs).
  * A module of a target (one with a directory of TCB/, e.g. `Arm`, as a
    component of its path) imports no module of another target: CI builds
    each target's modules in a shard of its own (ci/lean_shards.py), and
    what more than one target uses goes in a target-independent module.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean" / "VerifiedGarbage"

ALLOWED_IMPORTS = {
    "TCB": ("Lean", "VerifiedGarbage.TCB."),
    "Spec": ("VerifiedGarbage.TCB.", "VerifiedGarbage.Spec.", "Mathlib"),
    "Impl": ("VerifiedGarbage.TCB.", "VerifiedGarbage.Spec.", "VerifiedGarbage.Impl.", "Mathlib"),
}


def allowed(mod: str, prefixes: tuple[str, ...]) -> bool:
    return any(mod == p or mod.startswith(p if p.endswith(".") else p + ".") for p in prefixes)


def target_of(parts, targets: set[str]) -> str | None:
    return next((p for p in parts if p in targets), None)


def main() -> int:
    errors = []
    targets = {p.name for p in (LEAN / "TCB").iterdir() if p.is_dir()}
    for f in sorted(LEAN.rglob("*.lean")):
        own = target_of(f.relative_to(LEAN).with_suffix("").parts, targets)
        if own is None:
            continue
        for n, line in enumerate(f.read_text().splitlines(), 1):
            m = re.match(r"\s*import\s+(VerifiedGarbage\.\S+)", line)
            other = m and target_of(m.group(1).split("."), targets)
            if other and other != own:
                errors.append(f"{f.relative_to(ROOT)}:{n}: a module of {own} may not import {m.group(1)}, of {other}")
    for d, prefixes in ALLOWED_IMPORTS.items():
        for f in sorted((LEAN / d).rglob("*.lean")):
            for n, line in enumerate(f.read_text().splitlines(), 1):
                m = re.match(r"\s*import\s+(\S+)", line)
                if m and not allowed(m.group(1), prefixes):
                    errors.append(f"{f.relative_to(ROOT)}:{n}: {d}/ may not import {m.group(1)}")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("Lean imports OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
