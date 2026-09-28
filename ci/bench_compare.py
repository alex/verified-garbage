"""Compares the performance of two checkouts of this repository.

    python3 ci/bench_compare.py BASE HEAD [--summary FILE]

Both are built with HEAD's `bench/` crate (copied into BASE, so the two run
the same benchmark code against different library code), and their benchmark
binaries are run alternately on this machine, a few rounds each, keeping the
fastest time of each benchmark on each side: interleaving cancels out slow
drift in the machine's speed, and the minimum discards runs slowed by
interference, both of which are common on shared CI runners.

Writes a Markdown table of the results to stdout (and appends it to
`--summary`, e.g. `$GITHUB_STEP_SUMMARY`), and exits with status 1 if any
verified-garbage benchmark got slower by more than `--threshold`.

OpenSSL's code is the same on both sides, so its benchmarks run just once,
with HEAD's binary, as a reference point for HEAD's times.
"""

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import sys

# Criterion filters (regexes over benchmark ids, which are
# `<primitive>/<library>/<bytes>`, see bench/benches/primitives.rs).
VG = "verified-garbage"
OPENSSL = "openssl"


def build(checkout):
    """Builds the benchmarks of `checkout`, returning the binary's path."""
    out = subprocess.run(
        [
            "cargo",
            "bench",
            "--no-run",
            "--message-format=json-render-diagnostics",
        ],
        cwd=checkout / "bench",
        check=True,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout
    for line in out.splitlines():
        msg = json.loads(line)
        if msg.get("reason") == "compiler-artifact" and msg.get("executable"):
            if msg["target"]["name"] == "primitives":
                return msg["executable"]
    raise RuntimeError(f"no benchmark binary built in {checkout}")


def run(binary, home, library, args):
    """Runs the benchmarks once, returning each one's median time (ns)."""
    subprocess.run(
        [
            binary,
            "--bench",
            "--noplot",
            "--warm-up-time",
            str(args.warm_up_time),
            "--measurement-time",
            str(args.measurement_time),
            f"/{library}/",
        ],
        env={**os.environ, "CRITERION_HOME": str(home)},
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
    p.add_argument("--threshold", type=float, default=0.10)
    p.add_argument("--warm-up-time", type=float, default=0.5)
    p.add_argument("--measurement-time", type=float, default=2.0)
    p.add_argument("--work-dir", type=pathlib.Path, default=pathlib.Path("bench-compare"))
    args = p.parse_args()

    base, head = args.base.resolve(), args.head.resolve()
    if base != head:
        shutil.rmtree(base / "bench", ignore_errors=True)
        shutil.copytree(head / "bench", base / "bench", ignore=shutil.ignore_patterns("target"))
    binaries = {"base": build(base), "head": build(head)}

    shutil.rmtree(args.work_dir, ignore_errors=True)
    best = {"base": {}, "head": {}}
    for r in range(args.rounds):
        # Alternate which side goes first, so neither always runs warmer.
        for side in ("base", "head") if r % 2 == 0 else ("head", "base"):
            print(f"round {r + 1}/{args.rounds}: {side}", file=sys.stderr)
            times = run(binaries[side], args.work_dir.resolve() / f"{side}-{r}", VG, args)
            for bench_id, t in times.items():
                best[side][bench_id] = min(t, best[side].get(bench_id, t))
    print("OpenSSL", file=sys.stderr)
    openssl = run(binaries["head"], args.work_dir.resolve() / "openssl", OPENSSL, args)

    lines = [
        "## Benchmarks",
        "",
        f"Fastest of {args.rounds} interleaved runs of each side on this runner;"
        f" a slowdown of more than {args.threshold:.0%} fails."
        " OpenSSL (through rust-openssl) ran once, for reference.",
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
            change = f"{h / b - 1:+.1%}"
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
