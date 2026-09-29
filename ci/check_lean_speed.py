#!/usr/bin/env python3
"""Checks the rules in CLAUDE.md ("Keeping proofs fast") that can be checked
without building. Exits non-zero on violations.

  * No option changes a resource limit (`maxHeartbeats`, `maxRecDepth`,
    `synthInstance.maxHeartbeats`, `synthInstance.maxSize`), in a source file
    or in the lakefile. Lean's default `maxHeartbeats` (200000) bounds both
    elaboration and the kernel's check of every declaration, so a proof that
    got slow fails the build instead of quietly slowing it down.
  * No import of all of Mathlib or of `Mathlib.Tactic`.
  * No `simp` unfolds `runBlock` or `runStep`: step blocks with
    `runBlock_cons`, `runStep_some` and `runBlock_nil`. `Proof/Framework/`,
    which proves those lemmas and the generic rules about blocks, is exempt.
  * In the statement of a theorem in `Proof/`, an instruction-list literal
    (`[.op …]`) next to `++` has a type ascription (`([.op …] : List Instr)`):
    `++` elaborates its operands without an expected type, so each `.op`
    fails and is elaborated again, which cost up to seconds per statement.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean"
FRAMEWORK = LEAN / "VerifiedGarbage" / "Proof" / "Framework"

LIMITS = r"(?:maxHeartbeats|maxRecDepth|synthInstance\.maxHeartbeats|synthInstance\.maxSize)"
SET_LIMIT = re.compile(rf"\bset_option\s+{LIMITS}\b")
LAKEFILE_LIMIT = re.compile(rf"^\s*{LIMITS}\s*=", re.M)
BIG_IMPORT = re.compile(r"^\s*import\s+(Mathlib|Mathlib\.Tactic)\s*$", re.M)
SIMP_ARGS = re.compile(r"\bsimp(?:_all|a)?\b[^\[\n]*\[([^\]]*)\]")
UNFOLD = re.compile(r"(?<![\w.])(runBlock|runStep)(?![\w.])")
PROOF = LEAN / "VerifiedGarbage" / "Proof"
THEOREM = re.compile(r"^(?:private |protected )?(?:theorem|lemma) ", re.M)
DOT_LIST = re.compile(r"\[\s*\.")


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def unascribed_lists(text: str):
    """Yields the offsets of instruction-list literals in theorem statements
    that are an operand of `++` without a type ascription."""
    statements = [(m.start(), text.find(":=", m.end())) for m in THEOREM.finditer(text)]
    for m in DOT_LIST.finditer(text):
        i = m.start()
        if not any(a <= i < b for a, b in statements):
            continue
        depth, k = 0, i
        while k < len(text):
            depth += {"[": 1, "]": -1}.get(text[k], 0)
            if depth == 0:
                break
            k += 1
        before, after = text[:i].rstrip(), text[k + 1 :].lstrip()
        if not (before.endswith("++") or after.startswith("++")):
            continue
        if before.endswith("(") and after.startswith(":"):
            continue
        yield i


def main() -> int:
    errors = []
    sources = [f for f in LEAN.rglob("*.lean") if ".lake" not in f.parts]
    for f in sorted(sources):
        text = f.read_text()
        rel = f.relative_to(ROOT)
        for m in SET_LIMIT.finditer(text):
            errors.append(f"{rel}:{line_of(text, m.start())}: changes a resource limit; make the proof faster instead")
        for m in BIG_IMPORT.finditer(text):
            errors.append(f"{rel}:{line_of(text, m.start())}: imports {m.group(1)}; import the modules you use")
        if PROOF in f.parents:
            for i in unascribed_lists(text):
                errors.append(
                    f"{rel}:{line_of(text, i)}: instruction list next to `++` in a theorem statement; "
                    "ascribe it: `([.op …] : List Instr)`"
                )
        if FRAMEWORK in f.parents:
            continue
        for m in SIMP_ARGS.finditer(text):
            for u in UNFOLD.finditer(m.group(1)):
                errors.append(
                    f"{rel}:{line_of(text, m.start(1) + u.start())}: simp unfolds {u.group(1)}; "
                    "step with runBlock_cons, runStep_some and runBlock_nil"
                )
    lakefile = LEAN / "lakefile.toml"
    text = lakefile.read_text()
    for m in LAKEFILE_LIMIT.finditer(text):
        errors.append(f"{lakefile.relative_to(ROOT)}:{line_of(text, m.start())}: changes a resource limit")
    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print("Lean proof-speed rules OK")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
