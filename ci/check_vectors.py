#!/usr/bin/env python3
"""Checks vectors/sources.toml against the files under vectors/.

Every file under vectors/ (other than sources.toml itself) must be in one
of the directories of exactly one [[source]], so that it can be traced to
its upstream download.
"""

import pathlib
import sys
import tomllib

ROOT = pathlib.Path(__file__).resolve().parent.parent / "vectors"
MANIFEST = ROOT / "sources.toml"
KEYS = ("name", "directories", "url", "sha256", "retrieved")


def main() -> int:
    sources = tomllib.loads(MANIFEST.read_text())["source"]
    errors = []
    for source in sources:
        missing = [key for key in KEYS if key not in source]
        if missing:
            errors.append(f"source {source.get('name', '?')!r}: missing {', '.join(missing)}")
        elif not isinstance(source["directories"], list) or not source["directories"]:
            errors.append(f"source {source['name']!r}: directories must be a non-empty list")
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
        if not file.is_file() or file == MANIFEST:
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
