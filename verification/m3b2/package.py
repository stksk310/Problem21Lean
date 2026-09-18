"""Create the single review ZIP from committed source and local evidence."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
NAME = "P21_LEAN_M3B2_DPE_BOX_POSITIVE_EXIT_CANDIDATE_20260917.zip"
OUT = ROOT / "ci/candidate" / NAME
RECEIPT = ROOT / "ci/M3B2_CANDIDATE_SHA256.txt"


def sha(data): return hashlib.sha256(data).hexdigest()


tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=ROOT).decode().split("\0")
files = []
for name in tracked:
    if not name: continue
    path = Path(name)
    if path.parts[:2] == ("ci", "candidate") and path.suffix == ".zip": continue
    if name == "ci/M3B2_CANDIDATE_SHA256.txt": continue
    if (ROOT / path).is_file(): files.append(name)

required = ["README_M3B2.md", "SOURCE_OF_TRUTH_M3B2.md", "M3B2_STATEMENT_MAP.md",
            "M3B2_PROOF_ROUTE.md", "M3B2_DEPENDENCY_DAG.md", "NEXT_RESTART.md",
            "P21/Nonsymmetric/ColorCap/DPE/Exhaustion.lean",
            "P21/Nonsymmetric/ColorCap/FullColorCap.lean",
            "verification/m3b2/local-evidence/RESULTS.json"]
missing = [name for name in required if name not in files]
if missing: raise ValueError("Uncommitted/missing candidate input: " + repr(missing))

manifest = {name: sha((ROOT / name).read_bytes()) for name in files}
OUT.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(OUT, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
    for name in files: zf.write(ROOT / name, name)
    zf.writestr("M3B2_CANDIDATE_SOURCE_SHA256.json", json.dumps(manifest, indent=2) + "\n")
digest = sha(OUT.read_bytes())
RECEIPT.write_text(digest + "  " + NAME + "\n", encoding="utf-8", newline="\n")
print(str(OUT)); print(digest)
