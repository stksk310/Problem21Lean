#!/usr/bin/env python3
"""Build and inspect the deterministic lightweight Section 11 candidate."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
NAME = "P21_LEAN_FINAL_MAIN_THEOREM_CANDIDATE_20260923.zip"
OUT = ROOT / "delivery" / NAME
INTERNAL_MANIFEST = "FINAL_CANDIDATE_SOURCE_SHA256.json"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tracked_files() -> list[str]:
    names = subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", "ls-files"], cwd=ROOT, text=True
    ).splitlines()
    accepted = []
    for name in names:
        path = ROOT / name
        low = name.lower()
        if not path.is_file():
            continue
        if name.startswith("delivery/") or name.startswith("audit-evidence/"):
            continue
        if name.startswith("ci/candidate/"):
            continue
        if low.endswith(".zip") and not name.startswith("reference_inputs/"):
            continue
        if any(part in {".git", ".lake", "__pycache__", ".pytest_cache", ".pydeps"} for part in PurePosixPath(name).parts):
            continue
        accepted.append(name)
    return sorted(accepted)


def inspect_archive(path: Path) -> dict:
    with zipfile.ZipFile(path) as archive:
        infos = archive.infolist()
        names = [i.filename for i in infos]
        duplicates = sorted({name for name in names if names.count(name) > 1})
        unsafe = []
        symlinks = []
        forbidden = []
        for info in infos:
            pure = PurePosixPath(info.filename)
            if pure.is_absolute() or ".." in pure.parts:
                unsafe.append(info.filename)
            mode = info.external_attr >> 16
            if stat.S_ISLNK(mode):
                symlinks.append(info.filename)
            if any(p in {".git", ".lake"} for p in pure.parts):
                forbidden.append(info.filename)
            if info.filename != INTERNAL_MANIFEST and info.filename.lower().endswith(".zip") and not info.filename.startswith("reference_inputs/"):
                forbidden.append(info.filename)
        manifest = json.loads(archive.read(INTERNAL_MANIFEST))
        bad_hash = [name for name, expected in manifest.items() if name not in names or sha(archive.read(name)) != expected]
    report = {"entries": len(names), "duplicates": duplicates, "unsafe": unsafe, "symlinks": symlinks, "forbidden": sorted(set(forbidden)), "bad_hash": bad_hash}
    if any(report[key] for key in ("duplicates", "unsafe", "symlinks", "forbidden", "bad_hash")):
        raise RuntimeError(json.dumps(report, indent=2))
    return report


def main() -> None:
    files = tracked_files()
    required = {"P21/MainTheorem.lean", "P21Final.lean", "verification/final/MainStatementGate.lean", ".github/workflows/final-main-theorem-audit.yml"}
    missing = sorted(required - set(files))
    if missing:
        raise SystemExit("missing package inputs: " + ", ".join(missing))
    manifest = {name: sha((ROOT / name).read_bytes()) for name in files}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(OUT, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in files:
            info = zipfile.ZipInfo(name, (2026, 9, 23, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (ROOT / name).read_bytes())
        info = zipfile.ZipInfo(INTERNAL_MANIFEST, (2026, 9, 23, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        archive.writestr(info, json.dumps(manifest, indent=2, sort_keys=True).encode() + b"\n")
    report = inspect_archive(OUT)
    digest = sha(OUT.read_bytes())
    (ROOT / "delivery/FINAL_CANDIDATE_SHA256.txt").write_text(f"{digest}  {NAME}\n", encoding="utf-8", newline="\n")
    print(json.dumps({"path": str(OUT), "sha256": digest, "bytes": OUT.stat().st_size, **report}, indent=2))


if __name__ == "__main__":
    main()

