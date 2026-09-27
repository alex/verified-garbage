#!/usr/bin/env python3
"""Exports the coverage of an instrumented `cargo test` run as an lcov file.

Adapted from `process_rust_coverage` in pyca/cryptography's noxfile.py.

Usage: run `cargo test` with `RUSTFLAGS=-Cinstrument-coverage` and
`LLVM_PROFILE_FILE=<dir>/cov-%p-%m.profraw`, then, from the repository root
and with the same `RUSTFLAGS`:

    python3 ci/export_rust_coverage.py <dir>

This writes `<uuid>.lcov` in the current directory, containing only this
repository's files, with repository-relative `/`-separated paths, so lcov
files from different platforms can be merged by `ci/merge_rust_coverage.py`.
"""

import json
import os
import pathlib
import subprocess
import sys
import uuid

EXE = ".exe" if sys.platform == "win32" else ""


def test_binaries() -> list[str]:
    # `cargo test` has already built these; this only lists them.
    out = subprocess.run(
        ["cargo", "test", "--locked", "--no-run", "--message-format=json"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    binaries = []
    for line in out.splitlines():
        msg = json.loads(line)
        if (
            msg.get("reason") == "compiler-artifact"
            and msg["profile"]["test"]
            and msg.get("executable")
        ):
            binaries.append(msg["executable"])
    return binaries


def relative_records(lcov: str, root: pathlib.Path) -> str:
    """Keeps only records for files under `root`, with relative paths."""
    out = []
    for record in lcov.replace("\r\n", "\n").split("end_of_record\n"):
        lines = record.strip().splitlines()
        if not lines:
            continue
        assert lines[0].startswith("SF:"), lines[0]
        path = (root / lines[0][len("SF:") :]).resolve()
        try:
            rel = path.relative_to(root)
        except ValueError:
            continue  # the standard library or a dependency
        if rel.parts[0] == "target":
            continue
        out.append("\n".join([f"SF:{rel.as_posix()}", *lines[1:], "end_of_record"]))
    return "".join(line + "\n" for line in out)


def main(profraw_dir: str) -> None:
    root = pathlib.Path.cwd().resolve()
    libdir = subprocess.run(
        ["rustc", "--print", "target-libdir"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    bindir = pathlib.Path(libdir).parent / "bin"

    profraws = sorted(str(p) for p in pathlib.Path(profraw_dir).glob("*.profraw"))
    assert profraws, f"no .profraw files in {profraw_dir}"
    profdata = os.path.join(profraw_dir, "rust-cov.profdata")
    subprocess.run(
        [str(bindir / f"llvm-profdata{EXE}"), "merge", "-sparse", *profraws, "-o", profdata],
        check=True,
    )

    first, *rest = test_binaries()
    lcov = subprocess.run(
        [
            str(bindir / f"llvm-cov{EXE}"),
            "export",
            first,
            *(arg for b in rest for arg in ("-object", b)),
            f"-instr-profile={profdata}",
            "--format=lcov",
        ],
        check=True,
        capture_output=True,
        text=True,
    ).stdout

    out = f"{uuid.uuid4()}.lcov"
    with open(out, "w", newline="\n") as f:
        f.write(relative_records(lcov, root))
    print(f"wrote {out}")


if __name__ == "__main__":
    main(*sys.argv[1:])
