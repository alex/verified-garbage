#!/usr/bin/env python3
"""Checks the rules in CLAUDE.md ("Keeping proofs fast") that can be checked
without building. Exits non-zero on violations.

  * No option changes a resource limit (`maxHeartbeats`, `maxRecDepth`,
    `synthInstance.maxHeartbeats`, `synthInstance.maxSize`), in a source file
    or in the lakefile.
  * No import of all of Mathlib or of `Mathlib.Tactic`.
  * No `simp` unfolds `runBlock` or `runStep` (outside `Proof/Framework/`,
    which proves the lemmas that step blocks).
  * In the statement of a theorem in `Proof/`, an instruction-list literal
    (`[.op …]`) next to `++` has a type ascription (`([.op …] : List Instr)`).
  * A module that defines meta code (a tactic or command elaborator, a
    simproc, or a function in `MetaM`, `TacticM`, ...) and could be compiled
    (it imports only Lean core and modules of precompiled libraries) is in a
    precompiled library (`NativeTactics` in the lakefile): otherwise the
    interpreter runs it, an order of magnitude slower, in every module that
    uses it.
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
META = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:elab|elab_rules|simproc|dsimproc)\b"
    r"|^(?:(?:private|protected|partial|unsafe|noncomputable)\s+)*def\s[^\n]*"
    r"\b(?:CoreM|MetaM|SimpM|TermElabM|TacticM|CommandElabM)\b",
    re.M,
)
IMPORT = re.compile(r"^import\s+([\w.]+)", re.M)
LIB = re.compile(r"^\[\[lean_lib\]\]\n(.*?)(?=^\[\[|\Z)", re.M | re.S)


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


def precompiled_globs(lakefile: str) -> list[str]:
    """The module globs of the libraries with `precompileModules = true`."""
    globs = []
    for m in LIB.finditer(lakefile):
        block = m.group(1)
        if re.search(r"^precompileModules\s*=\s*true", block, re.M):
            g = re.search(r"^globs\s*=\s*\[(.*?)\]", block, re.M | re.S)
            if g:
                globs += re.findall(r'"([^"]+)"', g.group(1))
    return globs


def in_globs(module: str, globs: list[str]) -> bool:
    for g in globs:
        if g.endswith(".+") and module.startswith(g[:-1]):
            return True
        if g.endswith(".*") and (module == g[:-2] or module.startswith(g[:-1])):
            return True
        if module == g:
            return True
    return False


def uncompiled_meta(rel_module: str, text: str, globs: list[str]) -> bool:
    """Whether the module defines meta code, could be compiled (it imports only
    Lean core and precompiled modules), and is not."""
    if not META.search(text) or in_globs(rel_module, globs):
        return False
    core = ("Init", "Std", "Lean")
    return all(i.split(".")[0] in core or in_globs(i, globs) for i in IMPORT.findall(text))


def main() -> int:
    errors = []
    globs = precompiled_globs((LEAN / "lakefile.toml").read_text())
    sources = [f for f in LEAN.rglob("*.lean") if ".lake" not in f.parts]
    for f in sorted(sources):
        text = f.read_text()
        rel = f.relative_to(ROOT)
        module = ".".join(f.relative_to(LEAN).with_suffix("").parts)
        if uncompiled_meta(module, text, globs):
            errors.append(
                f"{rel}: defines meta code and imports only Lean core and precompiled modules; "
                "add it to `NativeTactics` in lean/lakefile.toml so that it runs compiled"
            )
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
