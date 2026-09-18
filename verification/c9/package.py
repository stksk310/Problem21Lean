"""Create the single principal C9 candidate archive."""
from pathlib import Path
import hashlib, json, subprocess, zipfile

ROOT = Path(__file__).resolve().parents[2]
NAME = "P21_LEAN_C9_CHAIN_TWO_PACKET_CANDIDATE_20260919.zip"
OUT = ROOT / "ci/candidate" / NAME
RECEIPT = ROOT / "ci/C9_CANDIDATE_SHA256.txt"
def sha(data: bytes) -> str: return hashlib.sha256(data).hexdigest()
files = [n for n in subprocess.check_output(
    ["git", "-c", f"safe.directory={ROOT.as_posix()}", "ls-files"], cwd=ROOT, text=True
).splitlines() if (ROOT/n).is_file() and not n.startswith("ci/candidate/") and n != "ci/C9_CANDIDATE_SHA256.txt"]
required = ["P21/Nonsymmetric/Chain/C9.lean", "P21/Nonsymmetric/Chain/C9/Handoff.lean",
            "P21/Nonsymmetric/Chain/C9/EuclideanSeed.lean", "verification/c9/verify.py",
            "README_C8.md", "README_C9.md", ".github/workflows/c9-audit.yml"]
missing = [x for x in required if x not in files]
if missing: raise RuntimeError("missing " + repr(missing))
manifest = {n:sha((ROOT/n).read_bytes()) for n in files}
OUT.parent.mkdir(parents=True, exist_ok=True)
with zipfile.ZipFile(OUT, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for n in files: z.write(ROOT/n, n)
    z.writestr("C9_CANDIDATE_SOURCE_SHA256.json", json.dumps(manifest, indent=2) + "\n")
digest = sha(OUT.read_bytes())
RECEIPT.write_text(f"{digest}  ci/candidate/{NAME}\n", encoding="utf-8", newline="\n")
print(OUT); print(digest)
