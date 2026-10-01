#!/usr/bin/env python3
"""Checks that the generated x86 code only runs the instructions affected by
MXCSR-configuration-dependent timing (MCDT) under Intel's mitigation, from
the generated code in `src/asm/x86_64/` and `src/asm/x86/`.

On some Intel processors, a few vector multiplies (Intel's list, "MCDT Data
Operand Independent Timing Instructions": `pmuludq`, `pmullw`, `pmulhw`,
their VEX/EVEX forms, and others the ISA models do not have yet) may take a
cycle longer for specific data values unless MXCSR holds `0x1FBF`. The
leakage model of the proofs does not see this (see "MCDT" in
`lean/VerifiedGarbage/TCB/X86_64/Isa.lean`), so this script checks that each
such instruction is inside a *protected region* of its function, which is
Intel's sequence, exactly:

* the prologue: `stmxcsr` (saving the caller's MXCSR), then, in the same
  straight-line code, `mov r32, 8127` (`0x1FBF`), `mov DWORD PTR [m], r32`,
  `ldmxcsr DWORD PTR [m]` and `lfence`, one after the other;
* the region: the code after that `lfence`, up to the next instruction that
  reads or writes MXCSR, which must be the epilogue's `ldmxcsr`;
* the epilogue: `lfence`, then straight-line `mov`s, then `ldmxcsr` of the
  slot the prologue's `stmxcsr` saved to. (That the value it loads is the
  caller's is proven: MXCSR's control bits are callee-saved in the
  contracts.)

A region is only entered through its prologue: no jump from outside it may
land inside it, and it may not contain a `call` or `ret`. The check is
conservative: it rejects every affected instruction outside a region,
whether or not its operands are secret.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ASM = ROOT / "src" / "asm"
TARGETS = ("x86", "x86_64")

# Intel, "MCDT Data Operand Independent Timing Instructions", Table 1.
AFFECTED = {
    "pmaddubsw", "pmaddwd", "pmuldq", "pmulhrsw", "pmulhuw", "pmulhw",
    "pmulld", "pmullw", "pmuludq",
    "vplzcntd", "vplzcntq", "vpmadd52huq", "vpmadd52luq", "vpmaddubsw",
    "vpmaddwd", "vpmuldq", "vpmulhrsw", "vpmulhuw", "vpmulhw", "vpmulld",
    "vpmullq", "vpmullw", "vpmuludq",
}  # fmt: skip

FN = re.compile(
    r"^pub\(crate\) unsafe extern \"[\w-]+\" fn (vg_\w+)\(.*?\)(?: -> [^{]+?)? \{\n(.*?)^\}",
    re.MULTILINE | re.DOTALL,
)
LINE = re.compile(r'^\s*"([^"]*)",$', re.MULTILINE)
LABEL = re.compile(r"^(\d+):$")
MXCSR_VALUE = {"8127", "0x1FBF", "0x1fbf"}


def code(body, first_line):
    """The function's instructions, the line of the file each is on, and
    where each numeric label is: the index of the instruction it precedes."""
    instrs, lines, labels = [], [], {}
    offset = 0
    line_number = first_line
    for m in LINE.finditer(body):
        line = m.group(1)
        label = LABEL.match(line)
        if label:
            labels.setdefault(label.group(1), []).append(len(instrs))
        else:
            instrs.append(line)
            # Count each newline once, rather than rescanning the growing
            # prefix for every instruction in large generated functions.
            line_number += body.count("\n", offset, m.start(1))
            offset = m.start(1)
            lines.append(line_number)
    return instrs, lines, labels


def mnemonic(instr):
    return instr.split(None, 1)[0]


def operands(instr):
    parts = instr.split(None, 1)
    return [o.strip() for o in parts[1].split(",")] if len(parts) > 1 else []


def is_branch(instr):
    return mnemonic(instr).startswith("j") or mnemonic(instr) in ("call", "ret")


def target(instr, i, labels):
    """The index a jump at `i` lands on, or `None` if it is not a jump to a
    numeric local label."""
    ops = operands(instr)
    m = re.fullmatch(r"(\d+)([fb])", ops[0]) if len(ops) == 1 else None
    if not m or m.group(1) not in labels:
        return None
    defs = labels[m.group(1)]
    if m.group(2) == "b":
        before = [d for d in defs if d <= i]
        return before[-1] if before else None
    after = [d for d in defs if d > i]
    return after[0] if after else None


def straight(instrs, lo, hi, labels):
    """Whether `instrs[lo:hi]` is straight-line code: no branch in it, and
    no label inside it."""
    inside = any(lo < d < hi for defs in labels.values() for d in defs)
    return not inside and not any(is_branch(x) for x in instrs[lo:hi])


def prologue(instrs, i, labels):
    """If `instrs[i]` is the `ldmxcsr` of Intel's prologue, the memory
    operand its `stmxcsr` saved MXCSR to; otherwise an error."""
    if i < 3 or i + 1 >= len(instrs) or instrs[i + 1] != "lfence":
        return None, "not followed by lfence"
    (slot,) = operands(instrs[i])
    load, store = instrs[i - 2], instrs[i - 1]
    lops, sops = operands(load), operands(store)
    if not (
        mnemonic(load) == "mov"
        and len(lops) == 2
        and lops[1] in MXCSR_VALUE
        and mnemonic(store) == "mov"
        and sops == [slot, lops[0]]
    ):
        return None, "not preceded by `mov r32, 8127` and a store of it to its operand"
    for j in range(i - 3, -1, -1):
        if mnemonic(instrs[j]) == "stmxcsr":
            if not straight(instrs, j, i + 2, labels):
                break
            return operands(instrs[j])[0], None
    return None, "not preceded by stmxcsr in the same straight-line code"


def check_function(name, instrs, lines, labels):
    errors = []

    def at(k):
        return f"{name}:{lines[k]}"

    regions = []  # (first, end): instrs[first:end] is protected
    i = 0
    while i < len(instrs):
        if mnemonic(instrs[i]) == "ldmxcsr":
            saved, why = prologue(instrs, i, labels)
            if why:
                errors.append(f"{at(i)}: `{instrs[i]}` is not Intel's MCDT prologue: {why}")
                i += 1
                continue
            first = i + 2
            end = first
            while end < len(instrs) and mnemonic(instrs[end]) not in ("ldmxcsr", "stmxcsr"):
                end += 1
            if end == len(instrs) or mnemonic(instrs[end]) != "ldmxcsr":
                errors.append(
                    f"{at(first - 1)}: the MCDT region after this prologue has no epilogue"
                )
                break
            fence = end - 1
            while fence >= first and mnemonic(instrs[fence]) == "mov":
                fence -= 1
            if (
                fence < first
                or instrs[fence] != "lfence"
                or not straight(instrs, fence, end + 1, labels)
                or operands(instrs[end]) != [saved]
            ):
                errors.append(
                    f"{at(end)}: `{instrs[end]}` is not Intel's MCDT epilogue: "
                    f"lfence, then straight-line movs, then ldmxcsr of {saved}"
                )
            regions.append((first, fence))
            i = end + 1
        else:
            i += 1

    def region_of(k):
        return next((r for r in regions if r[0] <= k < r[1]), None)

    for k, instr in enumerate(instrs):
        r = region_of(k)
        if mnemonic(instr) in AFFECTED and r is None:
            errors.append(
                f"{at(k)}: `{instr}` is outside Intel's MXCSR prologue and "
                "epilogue (MCDT, see lean/VerifiedGarbage/TCB/X86_64/Isa.lean)"
            )
        if not is_branch(instr):
            continue
        if r is not None and mnemonic(instr) in ("call", "ret"):
            errors.append(f"{at(k)}: `{instr}` is inside an MCDT region")
            continue
        if mnemonic(instr).startswith("j"):
            t = target(instr, k, labels)
            if t is None:
                if regions:
                    errors.append(f"{at(k)}: cannot resolve the target of `{instr}`")
                continue
            # Entering a region other than through its prologue; the
            # region's first instruction is entered by the prologue's
            # fall-through, or by a jump from inside the region (a loop).
            rt = next((q for q in regions if q[0] <= t < q[1]), None)
            if rt is not None and rt != r:
                errors.append(
                    f"{at(k)}: `{instr}` jumps into the MCDT region at "
                    f"line {lines[rt[0]]} from outside it"
                )
    return errors, len(regions)


def main():
    errors = []
    regions = 0
    for target_name in TARGETS:
        for path in sorted((ASM / target_name).glob("*.rs")):
            text = path.read_text()
            offset = 0
            first_line = 1
            for m in FN.finditer(text):
                name, body = m.groups()
                first_line += text.count("\n", offset, m.start(2))
                offset = m.start(2)
                instrs, lines, labels = code(body, first_line)
                where = f"{path.relative_to(ROOT)} ({name})"
                errs, n = check_function(where, instrs, lines, labels)
                errors += errs
                regions += n
    for e in errors:
        print(e, file=sys.stderr)
    if errors:
        return 1
    print(f"every MCDT-affected instruction is inside one of {regions} MXCSR-protected regions")
    return 0


if __name__ == "__main__":
    sys.exit(main())
