from pathlib import Path
import hashlib,json,subprocess,zipfile
ROOT=Path(__file__).resolve().parents[2]
NAME="P21_LEAN_C7_CHAIN_CORE_ROOT_CANDIDATE_20260918.zip"
OUT=ROOT/"ci/candidate"/NAME
RECEIPT=ROOT/"ci/C7_CANDIDATE_SHA256.txt"
def sha(b):return hashlib.sha256(b).hexdigest()
files=[n for n in subprocess.check_output(["git","ls-files"],cwd=ROOT,text=True).splitlines() if (ROOT/n).is_file() and not n.startswith("ci/candidate/") and n!="ci/C7_CANDIDATE_SHA256.txt"]
required=["README_C7.md","SOURCE_OF_TRUTH_C7.md","C7_STATEMENT_MAP.md","C7_PROOF_ROUTE.md","C7_DEPENDENCY_DAG.md","NEXT_RESTART.md","P21/Nonsymmetric/Chain/ShiftNew.lean","verification/c7/StatementGate.lean"]
missing=[x for x in required if x not in files]
if missing:raise RuntimeError("missing "+repr(missing))
manifest={n:sha((ROOT/n).read_bytes()) for n in files}
OUT.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(OUT,"w",zipfile.ZIP_DEFLATED,compresslevel=9) as z:
  for n in files:z.write(ROOT/n,n)
  z.writestr("C7_CANDIDATE_SOURCE_SHA256.json",json.dumps(manifest,indent=2)+"\n")
digest=sha(OUT.read_bytes());RECEIPT.write_text(
  f"{digest}  ci/candidate/{NAME}\n",encoding="utf-8",newline="\n")
print(OUT);print(digest)
