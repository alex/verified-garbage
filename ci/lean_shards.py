#!/usr/bin/env python3
"""Splits the Lean build into shards that CI builds on separate runners.

The Lean build is limited by throughput, not by the depth of its import
graph: one runner spends most of its time checking the proofs of one target
after another, although no target's proofs need another's. So CI builds one
shard per target, each with the modules whose name has that target's
directory (a subdirectory of `VerifiedGarbage/TCB/`, e.g. `Proof.Sha256.Arm.…`,
`Artifacts.Sha256.Arm`), and one shard, `common`, with the rest (the TCB, the
specifications, the framework and the golden tests). Each shard builds its
modules and whatever they import, and hands on the outputs of its own
modules; a final job puts them together, checks with `lake build` that
nothing is missing, and runs the emitter. A new target is a new shard,
without changing CI.

  lean_shards.py list            the shards, as a JSON list (for a matrix)
  lean_shards.py targets SHARD   the modules of SHARD, as `lake build`
                                 targets (`+Module`), one per line
  lean_shards.py outputs SHARD   of the paths on stdin (files under
                                 `lean/.lake/build/`, relative to it), those
                                 that are outputs of SHARD's modules
  lean_shards.py replay SHARD    the modules whose declarations SHARD replays
                                 through the kernel (`leanchecker`), one per
                                 line; `replay merge`, those the final job does

Every module (every file the lakefile's libraries build) is in exactly one
shard, so the shards' outputs together are the whole build.

`leanchecker M` replays `M` and every module whose name starts with `M.`, so
a module with a descendant in another shard (`VerifiedGarbage.Artifacts`,
over every target's registration files) is replayed, with its descendants,
by the final job, which has the whole build; each shard replays the rest of
its modules. Every module is replayed exactly once.
"""

import json
import pathlib
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent / "lean"
# The libraries of `lean/lakefile.toml`: `VerifiedGarbage.+` and
# `VerifiedGarbageTest.+` (every module under each, but not a root module).
LIBRARIES = ["VerifiedGarbage", "VerifiedGarbageTest"]
COMMON = "common"


def target_names() -> list[str]:
    return sorted(p.name for p in (LEAN / "VerifiedGarbage" / "TCB").iterdir() if p.is_dir())


def modules() -> list[str]:
    mods = []
    for lib in LIBRARIES:
        mods += [".".join(f.relative_to(LEAN).with_suffix("").parts) for f in (LEAN / lib).rglob("*.lean")]
    return sorted(mods)


def shard_of(module: str, names: list[str]) -> str:
    return next((part for part in module.split(".") if part in names), COMMON)


def replay_groups(mods: list[str], names: list[str]) -> dict[str, list[str]]:
    """The modules each shard (and `merge`, the final job) passes to
    `leanchecker`: each covers itself and its descendants."""
    cross = [m for m in mods if any(d.startswith(m + ".") and shard_of(d, names) != shard_of(m, names) for d in mods)]
    tops = [m for m in cross if not any(m.startswith(c + ".") for c in cross)]
    groups: dict[str, list[str]] = {"merge": tops}
    for m in mods:
        if not any(m == t or m.startswith(t + ".") for t in tops):
            groups.setdefault(shard_of(m, names), []).append(m)
    return groups


def module_of_output(path: str) -> str:
    """The module whose output `path` is: `lib/lean/A/B.olean.hash` and
    `ir/A/B.c` are outputs of `A.B`."""
    parts = pathlib.PurePosixPath(path).parts[1:]
    if parts and parts[0] == "lean":
        parts = parts[1:]
    return ".".join([*parts[:-1], parts[-1].split(".")[0]]) if parts else ""


def main(args: list[str]) -> int:
    names = target_names()
    shards = [*names, COMMON]
    if args == ["list"]:
        print(json.dumps(shards))
        return 0
    if len(args) == 2 and args[0] == "replay" and args[1] in [*shards, "merge"]:
        for m in replay_groups(modules(), names).get(args[1], []):
            print(m)
        return 0
    if len(args) == 2 and args[0] in ("targets", "outputs") and args[1] in shards:
        if args[0] == "targets":
            # `+`: a module, never a package or library of the same name.
            for m in modules():
                if shard_of(m, names) == args[1]:
                    print(f"+{m}")
        else:
            for line in sys.stdin:
                path = line.strip()
                if path and shard_of(module_of_output(path), names) == args[1]:
                    print(path)
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
