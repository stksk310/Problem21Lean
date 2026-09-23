#!/usr/bin/env python3
"""Create or verify the immutable pre-Section-11 Lean-source manifest."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = ROOT / "verification/final/FROZEN_SOURCE_SHA256.json"
BASE = "e4799d8044fd524a94b960ab19c333b08a8c93bb"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def base_paths() -> list[str]:
    output = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "ls-tree", "-r", "--name-only", BASE],
        cwd=ROOT,
    ).decode("utf-8").splitlines()
    return sorted(name for name in output if name.endswith(".lean"))


def write_manifest() -> None:
    files = {name: digest(ROOT / name) for name in base_paths()}
    MANIFEST.write_text(
        json.dumps({"base_commit": BASE, "files": files}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(f"WROTE {len(files)} frozen Lean hashes")


def check_manifest() -> None:
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    if data.get("base_commit") != BASE:
        raise SystemExit("frozen base mismatch")
    bad = []
    for name, expected in data.get("files", {}).items():
        path = ROOT / name
        if not path.is_file() or digest(path) != expected:
            bad.append(name)
    if bad:
        raise SystemExit("FROZEN source changed: " + ", ".join(bad))
    print(f"FROZEN SOURCE PASS ({len(data['files'])} Lean files at {BASE})")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    write_manifest() if args.write else check_manifest()


if __name__ == "__main__":
    main()
