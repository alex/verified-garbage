#!/usr/bin/env python3
"""Checks that no CI run of the tests with restricted CPU features repeats
another.

`VG_CPU_FEATURES` restricts the CPU features the library detects (with the
`cpu-features-env` feature). The `rust-cpu-features` job of
`.github/workflows/ci.yml` is the only place that sets it: each entry of
its matrix is one CPU (its `chip`, `arch`, `os` and `container`), whose
`runs` are lines of `<VG_CPU_FEATURES> | <tests>` (`-` for no restriction,
`all` for every test). This checks that

* nothing else in `ci.yml` sets `VG_CPU_FEATURES`, so every such run is
  one of these lines;
* each line is well formed, naming each test once, and `all` alone;
* each CPU has at most one line for each value of `VG_CPU_FEATURES`
  (across all its entries), so no run repeats or contains another: tests
  that need the same features on the same CPU go on one line.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW = ROOT / ".github" / "workflows" / "ci.yml"
JOB = "rust-cpu-features"
# What a run's CPU is: the same values of these, in entries of the
# matrix, are the same CPU.
MACHINE = ("chip", "arch", "os", "container.image", "container.options")

JOB_START = re.compile(r"^  ([\w-]+):\s*$")
ENTRY = re.compile(r"^ {10}- ([\w-]+):\s*(.*)$")
KEY = re.compile(r"^ {12}([\w-]+):\s*(.*)$")
SUBKEY = re.compile(r"^ {14}([\w-]+):\s*(.*)$")


def job_lines(text, job):
    """The lines of `job` in the workflow, with their line numbers."""
    lines = text.splitlines()
    out, inside = [], False
    for n, line in enumerate(lines, 1):
        m = JOB_START.match(line)
        if m:
            inside = m.group(1) == job
            continue
        if inside:
            out.append((n, line))
    return out


def entries(text):
    """The `include` entries of the job's matrix: dicts of their keys
    (`container.image` for nested ones), with `runs` as a list of
    (line number, text) and `line` the entry's first line."""
    result, entry, block, nested = [], None, None, None
    in_include = False
    for n, line in job_lines(text, JOB):
        if line.strip() == "include:":
            in_include = True
            continue
        if not in_include:
            continue
        stripped = line.strip()
        if stripped.startswith("#") or not stripped:
            continue
        indent = len(line) - len(line.lstrip())
        if indent <= 8:
            break
        if block is not None and indent > 12:
            entry[block].append((n, stripped))
            continue
        block = None
        if nested is not None and indent > 12:
            m = SUBKEY.match(line)
            if m:
                entry[f"{nested}.{m.group(1)}"] = m.group(2)
            continue
        nested = None
        m = ENTRY.match(line) or KEY.match(line)
        if not m:
            continue
        if ENTRY.match(line):
            entry = {"line": n}
            result.append(entry)
        key, value = m.groups()
        if value == "|":
            entry[key], block = [], key
        elif value == "":
            nested = key
        else:
            entry[key] = value
    return result


def errors(text):
    errs = []
    lines = text.splitlines()
    job = {n for n, _ in job_lines(text, JOB)}
    for n, line in enumerate(lines, 1):
        if "VG_CPU_FEATURES" in line and not line.strip().startswith("#") and n not in job:
            errs.append(f"ci.yml:{n}: sets VG_CPU_FEATURES outside `{JOB}`: make it a line of a `runs` there")
    found = entries(text)
    if not found:
        errs.append(f"ci.yml: no matrix entries found in `{JOB}`")
    seen = {}
    for e in found:
        if "runs" not in e:
            errs.append(f"ci.yml:{e['line']}: an entry of `{JOB}` without `runs`")
            continue
        machine = tuple(e.get(k, "") for k in MACHINE)
        for n, run in e["runs"]:
            features, sep, tests = run.partition("|")
            features, names = features.strip(), tests.split()
            if not sep or not features or not names:
                errs.append(f"ci.yml:{n}: not `<VG_CPU_FEATURES> | <tests>`: {run}")
                continue
            if len(set(names)) != len(names):
                errs.append(f"ci.yml:{n}: a test named twice: {run}")
            if "all" in names and len(names) > 1:
                errs.append(f"ci.yml:{n}: `all` with other tests: {run}")
            if (machine, features) in seen:
                errs.append(
                    f"ci.yml:{n}: VG_CPU_FEATURES={features} again on this CPU (line {seen[machine, features]}): "
                    "put its tests on that line"
                )
            else:
                seen[machine, features] = n
    return errs


def main():
    errs = errors(WORKFLOW.read_text())
    for e in errs:
        print(e, file=sys.stderr)
    return 1 if errs else 0


if __name__ == "__main__":
    sys.exit(main())
