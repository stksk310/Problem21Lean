#!/usr/bin/env python3
"""Create and verify source and audit-evidence SHA-256 manifests."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EVIDENCE = ROOT / "delivery/P21_FINAL_TRUE_AUDIT_EVIDENCE"
SOURCE_MANIFEST = EVIDENCE / "VERIFIED_SOURCE_SHA256.json"
EVIDENCE_MANIFEST = EVIDENCE / "EVIDENCE_SHA256.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files() -> list[Path]:
    paths = list((ROOT / "P21").rglob("*.lean"))
    paths += [ROOT / "P21.lean", ROOT / "P21Final.lean"]
    paths += [
        p for p in (ROOT / "verification").rglob("*")
        if p.is_file()
        and p.suffix in {".lean", ".py", ".ps1", ".json"}
        and not any(part in {".pydeps", "__pycache__"} for part in p.relative_to(ROOT).parts)
    ]
    paths += [p for p in (ROOT / ".github/workflows").glob("*.yml") if p.is_file()]
    return sorted(set(paths))


def write() -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    sources = {p.relative_to(ROOT).as_posix(): sha(p) for p in source_files()}
    SOURCE_MANIFEST.write_text(json.dumps(sources, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    evidence = {
        p.name: sha(p) for p in sorted(EVIDENCE.iterdir())
        if p.is_file() and p.name != EVIDENCE_MANIFEST.name
    }
    EVIDENCE_MANIFEST.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")
    print(f"SOURCE MANIFEST: {len(sources)} files")
    print(f"EVIDENCE MANIFEST: {len(evidence)} files")


def verify() -> None:
    source = json.loads(SOURCE_MANIFEST.read_text(encoding="utf-8"))
    bad_source = [name for name, expected in source.items() if not (ROOT / name).is_file() or sha(ROOT / name) != expected]
    evidence = json.loads(EVIDENCE_MANIFEST.read_text(encoding="utf-8"))
    actual_names = {p.name for p in EVIDENCE.iterdir() if p.is_file() and p.name != EVIDENCE_MANIFEST.name}
    missing = sorted(set(evidence) - actual_names)
    extra = sorted(actual_names - set(evidence))
    bad_evidence = [name for name, expected in evidence.items() if (EVIDENCE / name).is_file() and sha(EVIDENCE / name) != expected]
    report = {"verified": not (bad_source or missing or extra or bad_evidence), "source_files": len(source), "evidence_files": len(evidence), "bad_source": bad_source, "missing": missing, "extra": extra, "bad_evidence": bad_evidence}
    print(json.dumps(report, indent=2))
    if not report["verified"]:
        raise SystemExit("manifest verification failed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    verify() if args.verify else write()
