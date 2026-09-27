#!/usr/bin/env python3
"""Structural invariants that keep the trusted base small and every piece of
emitted assembly verified. Run from anywhere; exits non-zero on violations.

Lean (lean/VerifiedGarbage/):
  * TCB/   imports only Lean core and TCB/  (no Mathlib: smaller trusted base).
  * Spec/  imports only TCB/, Spec/ and Mathlib.
  * Impl/  imports only TCB/, Spec/, Impl/ and Mathlib (never proofs).

Rust:
  * Assembly (`asm!`, `naked_asm!`, `global_asm!`, naked functions) and
    foreign code (`extern` blocks, `#[link]`) appear only in the generated
    src/asm/ modules.
  * There is no build script.
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

RUST_FORBIDDEN = [
    (re.compile(r"\b(asm|naked_asm|global_asm)!"), "inline assembly"),
    (re.compile(r"#\[\s*(unsafe\s*\(\s*)?naked"), "naked function"),
    (re.compile(r"\bextern\s+(\"[^\"]*\"\s*)?\{"), "extern block"),
    (re.compile(r"#\[\s*link\b"), "#[link]"),
]


def main() -> int:
    errors = []

    for d, allowed in ALLOWED_IMPORTS.items():
        for f in sorted((LEAN / d).rglob("*.lean")):
            for n, line in enumerate(f.read_text().splitlines(), 1):
                m = re.match(r"\s*import\s+(\S+)", line)
                if not m:
                    continue
                mod = m.group(1)
                if not any(mod == a or mod.startswith(a if a.endswith(".") else a + ".") for a in allowed):
                    errors.append(f"{f.relative_to(ROOT)}:{n}: {d}/ may not import {mod}")

    generated = ROOT / "src" / "asm"
    for f in sorted(ROOT.glob("**/*.rs")):
        rel = f.relative_to(ROOT)
        if rel.parts[0] in ("target", "vendor") or generated in f.parents:
            continue
        for n, line in enumerate(f.read_text().splitlines(), 1):
            code = line.split("//", 1)[0]
            for pat, what in RUST_FORBIDDEN:
                if pat.search(code):
                    errors.append(f"{rel}:{n}: {what} outside the generated src/asm/")

    if (ROOT / "build.rs").exists():
        errors.append("build.rs: the crate must not have a build script")

    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("structure OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
