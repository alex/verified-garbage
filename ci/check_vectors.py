#!/usr/bin/env python3
"""Checks vectors/sources/ against the files under vectors/.

Each vectors/sources/<name>.toml is one source: its `directories` hold
files extracted unmodified from the download at `url` (whose SHA-256 is
`sha256`), and .gitattributes keeps git from touching their line endings.
One file per source, so that PRs adding vectors add a file rather than
editing a shared one.

Every other file under vectors/ must be in one of the directories of
exactly one source, so that it can be traced to its upstream download.
"""

import pathlib
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent / "vectors"
SOURCES = ROOT / "sources"
KEYS = ("name", "directories", "url", "sha256", "retrieved")


def main() -> int:
    errors = []
    sources = []
    for path in sorted(SOURCES.iterdir()):
        if path.suffix != ".toml":
            errors.append(f"sources/{path.name}: not a .toml file")
            continue
        source = tomllib.loads(path.read_text())
        sources.append(source)
        missing = [key for key in KEYS if key not in source]
        if missing:
            errors.append(f"sources/{path.name}: missing {', '.join(missing)}")
        elif not isinstance(source["directories"], list) or not source["directories"]:
            errors.append(f"sources/{path.name}: directories must be a non-empty list")
        else:
            for directory in source["directories"]:
                if not (ROOT / directory).is_dir():
                    errors.append(f"{directory}: not a directory")
    dirs = [
        pathlib.PurePosixPath(d)
        for s in sources
        if isinstance(s.get("directories"), list)
        for d in s["directories"]
    ]
    count = 0
    for file in sorted(ROOT.rglob("*")):
        if not file.is_file() or SOURCES in file.parents:
            continue
        path = pathlib.PurePosixPath(file.relative_to(ROOT).as_posix())
        owners = [d for d in dirs if d in path.parents]
        if len(owners) != 1:
            errors.append(f"{path}: covered by {len(owners)} sources, not 1")
        count += 1
    for error in errors:
        print(f"vectors/{error}", file=sys.stderr)
    if not errors:
        print(f"Test vectors OK ({count} files, {len(sources)} sources)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
