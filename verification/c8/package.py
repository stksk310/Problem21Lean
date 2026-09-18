from pathlib import Path
import hashlib,json,subprocess,zipfile
ROOT=Path(__file__).resolve().parents[2]
NAME="P21_LEAN_C8_CHAIN_BOUNDARY_WINDOW_CANDIDATE_20260919.zip"
OUT=ROOT/"ci/candidate"/NAME
RECEIPT=ROOT/"ci/C8_CANDIDATE_SHA256.txt"
def sha(b):return hashlib.sha256(b).hexdigest()
files=[n for n in subprocess.check_output(["git","ls-files"],cwd=ROOT,text=True).splitlines() if (ROOT/n).is_file() and not n.startswith("ci/candidate/") and n!="ci/C8_CANDIDATE_SHA256.txt"]
required=["P21/Nonsymmetric/Chain/C8.lean","P21/Nonsymmetric/Chain/C8/Handoff.lean","verification/c8/StatementGate.lean","verification/c8/GeneratedAxiomCheck.lean","verification/c8/verify.py"]
missing=[x for x in required if x not in files]
if missing:raise RuntimeError("missing "+repr(missing))
manifest={n:sha((ROOT/n).read_bytes()) for n in files}
OUT.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(OUT,"w",zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for n in files:z.write(ROOT/n,n)
  z.writestr("C8_CANDIDATE_SOURCE_SHA256.json",json.dumps(manifest,indent=2)+"\n")
digest=sha(OUT.read_bytes());RECEIPT.write_text(
  f"{digest}  ci/candidate/{NAME}\n",encoding="utf-8",newline="\n")
print(OUT);print(digest)
