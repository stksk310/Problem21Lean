"""Verify the non-self-referential C9 evidence SHA-256 manifest."""
from pathlib import Path
import hashlib, json, sys

root = Path(sys.argv[1] if len(sys.argv) > 1 else "audit-evidence/c9")
manifest = root / "EVIDENCE_SHA256.json"
data = json.loads(manifest.read_text(encoding="utf-8"))
expected = data["files"]
actual = {p.name for p in root.iterdir() if p.is_file() and p.name != manifest.name}
if actual != set(expected):
    raise SystemExit(f"evidence file set mismatch: missing={set(expected)-actual}, extra={actual-set(expected)}")
for name, digest in expected.items():
    if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
        raise SystemExit(f"digest mismatch: {name}")
print(f"verified {len(expected)} evidence files")
