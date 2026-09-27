#!/usr/bin/env python3
"""Checks the import discipline between the directories of
lean/VerifiedGarbage/, which keeps the trusted base small and separate from
proofs. Exits non-zero on violations.

  * TCB/   imports only Lean core and TCB/  (no Mathlib: smaller trusted base).
  * Spec/  imports only TCB/, Spec/ and Mathlib.
  * Impl/  imports only TCB/, Spec/, Impl/ and Mathlib (never proofs).
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


def main() -> int:
    errors = []
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
