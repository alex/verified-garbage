"""Compares the performance of two checkouts of this repository.

    python3 ci/bench_compare.py BASE HEAD [--summary FILE]

Both are built with HEAD's `bench/` crate (copied into BASE, so the two run
the same benchmark code against different library code); if that doesn't
build against BASE (it benchmarks an API BASE doesn't have yet), BASE uses
its own `bench/` crate, and HEAD's other benchmarks show as new. Their benchmark
binaries are run alternately on this machine, a few rounds each, keeping the
fastest time of each benchmark on each side: interleaving cancels out slow
drift in the machine's speed, and the minimum discards runs slowed by
interference, both of which are common on shared CI runners.

Writes a Markdown table of the results to stdout (and appends it to
`--summary`, e.g. `$GITHUB_STEP_SUMMARY`), and exits with status 1 if any
verified-garbage benchmark got slower by more than `--threshold`.

OpenSSL's code is the same on both sides, so its benchmarks run just once,
with HEAD's binary, as a reference point for HEAD's times.

`VG_CPU_FEATURES` in the environment (see src/cpu.rs) restricts the CPU
features both sides use, and is named in the report. Each side is passed
only the features its own src/cpu.rs knows (base may predate one), since it
cannot use the others anyway.

`--modules` runs only the benchmarks of those library modules (see
`bench_arches.py`).
"""

import argparse
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys

# Criterion filters (regexes over benchmark ids, which are
# `<primitive>/<library>/<bytes>`, see bench/benches/primitives.rs).
VG = "verified-garbage"
OPENSSL = "openssl"


# Every build shares one target directory, so the dependencies (criterion,
# rust-openssl), which are the same on both sides, are compiled only once.
TARGET = pathlib.Path("bench-target").resolve()


def build(bench):
    """Builds the benchmark crate `bench`, returning the binary's path."""
    out = subprocess.run(
        [
            "cargo",
            "bench",
            "--no-run",
            "--message-format=json-render-diagnostics",
        ],
        cwd=bench,
        env={**os.environ, "CARGO_TARGET_DIR": str(TARGET)},
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get("reason") == "compiler-artifact" and msg.get("executable"):
            if msg["target"]["name"] == "primitives":
                # A copy, which the next build can't overwrite.
                binary = TARGET / f"primitives-{len(list(TARGET.glob('primitives-*')))}"
                shutil.copy2(msg["executable"], binary)
                return str(binary)
    raise RuntimeError(f"no benchmark binary built in {bench}")


def build_base(base, head):
    """Builds BASE's benchmarks (see the module docstring), returning the
    binary's path and a note on which benchmark code it runs, or no path
    if neither builds."""
    if base == head:
        return build(head / "bench"), None
    # A sibling of BASE's own `bench/`, so its `path = ".."` is BASE too.
    copy = base / "bench-head"
    shutil.rmtree(copy, ignore_errors=True)
    shutil.copytree(head / "bench", copy, ignore=shutil.ignore_patterns("target"))
    try:
        return build(copy), None
    except subprocess.CalledProcessError:
        pass
    if (base / "bench").is_dir():
        try:
            return build(base / "bench"), "Head's benchmarks don't build against base, so base ran its own."
        except subprocess.CalledProcessError:
            pass
    return None, "Base has no benchmarks that build, so head ran alone."


NAMES = re.compile(r"const NAMES: \[&str; \d+\] = \[(.*?)\];", re.DOTALL)


def cpu_features(checkout):
    """`VG_CPU_FEATURES` without the features `checkout`'s src/cpu.rs does
    not know (which it rejects)."""
    features = os.environ.get("VG_CPU_FEATURES", "")
    if features in ("", "none"):
        return features
    known = re.findall(r'"([^"]+)"', NAMES.search((checkout / "src/cpu.rs").read_text())[1])
    return ",".join(f for f in features.split(",") if f in known) or "none"


def run(binary, home, library, args, checkout):
    """Runs the benchmarks of `checkout` once, returning each one's median
    time (ns)."""
    subprocess.run(
        [
            binary,
            "--bench",
            "--noplot",
            "--warm-up-time",
            str(args.warm_up_time),
            "--measurement-time",
            str(args.measurement_time),
            # Only the median is used, not the bootstrapped confidence
            # intervals, whose default 100000 resamples cost more than a
            # short measurement.
            "--nresamples",
            "1000",
            f"/{library}/",
        ],
        env={
            **os.environ,
            "CRITERION_HOME": str(home),
            "VG_BENCH_MODULES": args.modules,
            "VG_CPU_FEATURES": cpu_features(checkout),
        },
        check=True,
        stdout=subprocess.DEVNULL,
    )
    times = {}
    for est in home.glob(f"*/{library}/*/new/estimates.json"):
        primitive, _, size = est.relative_to(home).parts[:3]
        times[primitive, int(size)] = json.loads(est.read_text())["median"]["point_estimate"]
    return times


def vs_openssl(ours, theirs):
    """How head's time compares with OpenSSL's, in words."""
    if ours > theirs * 1.05:
        return f"{ours / theirs:.1f}× slower"
    if theirs > ours * 1.05:
        return f"{theirs / ours:.1f}× faster"
    return "about the same"


def fmt_time(ns):
    for unit, scale in (("ms", 1e6), ("µs", 1e3)):
        if ns >= scale:
            return f"{ns / scale:.2f} {unit}"
    return f"{ns:.0f} ns"


def main():
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("base", type=pathlib.Path)
    p.add_argument("head", type=pathlib.Path)
    p.add_argument("--summary", type=pathlib.Path)
    p.add_argument("--rounds", type=int, default=3)
    p.add_argument("--threshold", type=float, default=0.25)
    p.add_argument("--warm-up-time", type=float, default=0.2)
    p.add_argument("--measurement-time", type=float, default=0.5)
    p.add_argument("--work-dir", type=pathlib.Path, default=pathlib.Path("bench-compare"))
    p.add_argument("--modules", default="", help="space-separated; only benchmark these modules")
    args = p.parse_args()

    base, head = args.base.resolve(), args.head.resolve()
    binaries = {"head": build(head / "bench")}
    binaries["base"], note = build_base(base, head)

    shutil.rmtree(args.work_dir, ignore_errors=True)
    best = {"base": {}, "head": {}}
    for r in range(args.rounds):
        # Alternate which side goes first, so neither always runs warmer.
        for side in ("base", "head") if r % 2 == 0 else ("head", "base"):
            if binaries[side] is None:
                continue
            print(f"round {r + 1}/{args.rounds}: {side}", file=sys.stderr)
            checkout = base if side == "base" else head
            times = run(binaries[side], args.work_dir.resolve() / f"{side}-{r}", VG, args, checkout)
            for bench_id, t in times.items():
                best[side][bench_id] = min(t, best[side].get(bench_id, t))
    print("OpenSSL", file=sys.stderr)
    openssl = run(binaries["head"], args.work_dir.resolve() / "openssl", OPENSSL, args, head)

    cpu_features = os.environ.get("VG_CPU_FEATURES", "")
    lines = [
        f"## Benchmarks (VG_CPU_FEATURES={cpu_features})" if cpu_features else "## Benchmarks",
        "",
        f"Fastest of {args.rounds} interleaved runs of each side on this runner;"
        f" a slowdown of more than {args.threshold:.0%} fails."
        " OpenSSL (through rust-openssl) ran once, for reference.",
        *(
            [
                f"Changed modules: {args.modules}. Only the benchmarks that use them ran"
                " (all of them, if one of these modules has no benchmark)."
            ]
            if args.modules.strip()
            else []
        ),
        *([f"{note}"] if note else []),
        "",
        "| Benchmark | Base | Head | Change | OpenSSL | Head vs OpenSSL |",
        "|---|--:|--:|--:|--:|--:|",
    ]
    regressions = []
    for primitive, size in sorted(best["head"]):
        bench_id = f"{primitive}/{size}"
        b, h = best["base"].get((primitive, size)), best["head"][primitive, size]
        if b is None:
            change = "new"
        else:
            change = f"{h / b - 1:.1%} slower" if h > b else f"{1 - h / b:.1%} faster"
            if h / b - 1 > args.threshold:
                regressions.append(bench_id)
                change += " 🚨"
        o = openssl.get((primitive, size))
        vs = vs_openssl(h, o) if o else "–"
        o = fmt_time(o) if o else "–"
        b = fmt_time(b) if b else "–"
        lines.append(f"| `{bench_id}` | {b} | {fmt_time(h)} | {change} | {o} | {vs} |")
    lines.append("")
    if regressions:
        lines.append(f"🚨 {len(regressions)} benchmark(s) slowed down by more than {args.threshold:.0%}.")
    else:
        lines.append(f"No benchmark slowed down by more than {args.threshold:.0%}.")
    report = "\n".join(lines) + "\n"

    print(report)
    if args.summary:
        with args.summary.open("a") as f:
            f.write(report)
    return 1 if regressions else 0


if __name__ == "__main__":
    sys.exit(main())
