"""Fresh P5 verification and evidence generation."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "verification/p5"
EVIDENCE = ROOT / "audit-evidence/p5"
BASE = "fd4ea0c7cbc57df6e935790a1387242bcf9e0087"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

def sha(data): return hashlib.sha256(data).hexdigest()
def write(name, text):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE/name).write_text(text, encoding="utf-8", newline="\n")
def run(cmd, log, append=False):
    p = subprocess.run(cmd, cwd=ROOT, text=True, encoding="utf-8", errors="replace",
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    mode = "a" if append else "w"
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    with (EVIDENCE/log).open(mode, encoding="utf-8", newline="\n") as f:
        f.write("$ " + " ".join(cmd) + "\n" + p.stdout + f"\nEXIT={p.returncode}\n")
    if p.returncode: raise RuntimeError(f"failed: {' '.join(cmd)}")
    return p.stdout
def lake(): return ["lake"]
def git(*args): return subprocess.check_output(["git", *args], cwd=ROOT).decode()

def protected_files():
    return [p for p in git("ls-tree","-r","--name-only",BASE,"P21").splitlines() if p.endswith(".lean")]
def integrity():
    names = protected_files(); bad=[]; manifest={}
    for name in names:
        old = subprocess.check_output(["git","show",f"{BASE}:{name}"], cwd=ROOT)
        manifest[name]=sha(old)
        path=ROOT/name
        if not path.is_file() or sha(path.read_bytes()) != manifest[name]: bad.append(name)
    (HERE/"FROZEN_SHA256.json").write_text(json.dumps({"commit":BASE,"files":manifest},indent=2)+"\n",encoding="utf-8")
    write("FROZEN_SOURCE_INTEGRITY.txt", f"Base: {BASE}\nProtected files: {len(names)}\nSOURCE_CHANGED: {'YES' if bad else 'NO'}\n" + "\n".join(bad)+"\n")
    if bad: raise RuntimeError("frozen source changed")

def modules():
    base=set(protected_files())
    paths=sorted(p for p in (ROOT/"P21/Nonsymmetric/Path").glob("*.lean") if p.relative_to(ROOT).as_posix() not in base)
    mods=[p.relative_to(ROOT).with_suffix("").as_posix().replace("/",".") for p in paths]
    write("P5_MODULE_LIST.txt", "\n".join(mods)+"\n")
    return mods

def debt():
    forbidden=re.compile(r"\b(sorry|admit|axiom|sorryAx|run_tac|native_decide)\b|\bunsafe\s+(?:theorem|def)\b|\bopaque\b")
    hits=[]
    for p in sorted((ROOT/"P21/Nonsymmetric/Path").glob("*.lean")):
        for n,line in enumerate(p.read_text(encoding="utf-8").splitlines(),1):
            code=line.split("--",1)[0]
            if forbidden.search(code): hits.append(f"{p.relative_to(ROOT)}:{n}:{line}")
    write("PROOF_DEBT_REPORT.txt", "PROOF DEBT: 0\n" if not hits else "\n".join(hits)+"\n")
    if hits: raise RuntimeError("proof debt")

def dag():
    graph={}
    for p in sorted((ROOT/"P21").rglob("*.lean")):
        mod=p.relative_to(ROOT).with_suffix("").as_posix().replace("/",".")
        graph[mod]=re.findall(r"^import\s+([\w.]+)",p.read_text(encoding="utf-8-sig"),re.M)
    active=set(); done=set()
    def visit(n):
        if n in active: raise RuntimeError("circular import "+n)
        if n in done:return
        active.add(n)
        for c in graph.get(n,[]):visit(c)
        active.remove(n);done.add(n)
    for n in graph:visit(n)
    root="P21.Nonsymmetric.Path.Exclusion"; seen=set()
    def collect(n):
        if n in seen:return
        seen.add(n)
        for c in graph.get(n,[]):collect(c)
    collect(root)
    forbidden={"P21.Nonsymmetric.Path.Integration","P21.Nonsymmetric.ColorCap.FullColorCap"}
    bad=sorted(seen&forbidden)
    write("DEPENDENCY_DAG_CHECK.txt",json.dumps(graph,indent=2)+"\nIMPORT DAG: ACYCLIC\n")
    write("CIRCULARITY_CHECK.txt","P5 exclusion imports:\n"+"\n".join(sorted(seen))+"\nFORBIDDEN="+repr(bad)+"\n")
    if bad: raise RuntimeError("reverse dependency")

def regressions():
    groups={
      "M1_ORIGINAL_SUITE.txt":["verification/StatementCheck.lean","verification/AxiomCheck.lean"],
      "M2A_ORIGINAL_SUITE.txt":["verification/m2/StableCoreRegression.lean","verification/m2/BranchIIRegression.lean"],
      "M2B_ORIGINAL_SUITE.txt":["verification/m2b/Regression.lean"],
      "M3A_ORIGINAL_SUITE.txt":["verification/m3/M3Regression.lean","verification/m3/ExtractionRegression.lean"],
      "M3B1_ORIGINAL_SUITE.txt":["verification/m3b1/StatementRegression.lean"],
      "M3B2_ORIGINAL_SUITE.txt":[str(p.relative_to(ROOT)).replace('\\','/') for p in sorted((ROOT/'verification/m3b2').glob('*Regression.lean'))]
    }
    for log,files in groups.items():
        for i,f in enumerate(files): run(lake()+["env","lean",f],log,append=i>0)

def main():
    EVIDENCE.mkdir(parents=True,exist_ok=True)
    write("RUN_CONTEXT.json",json.dumps({"branch":git("branch","--show-current").strip(),"commit":git("rev-parse","HEAD").strip(),"github_run_id":os.getenv("GITHUB_RUN_ID"),"github_run_attempt":os.getenv("GITHUB_RUN_ATTEMPT")},indent=2)+"\n")
    write("COMMIT_SHA.txt",git("rev-parse","HEAD"))
    write("ENVIRONMENT.txt",run(lake()+["--version"],"_env.tmp")+run(["lean","--version"],"_lean.tmp"))
    integrity(); debt(); dag(); mods=modules()
    run(lake()+["build"],"ROOT_BUILD_LOG.txt")
    run(lake()+["build",*mods],"P5_BUILD_LOG.txt")
    run(lake()+["env","lean","verification/p5/StatementGate.lean"],"STATEMENT_INSPECTION.txt")
    ax=run(lake()+["env","lean","verification/p5/GeneratedAxiomCheck.lean"],"AXIOM_REPORT.txt")
    roots=set(re.findall(r"\b(?:propext|Classical\.choice|Quot\.sound|[A-Za-z0-9_.]+Ax)\b",ax)); bad=roots-ALLOWED_AXIOMS
    write("AXIOM_SUMMARY.json",json.dumps({"allowed":sorted(ALLOWED_AXIOMS),"observed":sorted(roots),"project_specific_axioms":len(bad)},indent=2)+"\n")
    if bad: raise RuntimeError("unexpected axioms "+repr(bad))
    run(lake()+["env","lean","verification/p5/StatementGate.lean"],"P5_VERIFICATION_LOG.txt")
    regressions(); integrity(); debt(); dag()
    tracked=[x for x in git("ls-files").splitlines() if (ROOT/x).is_file()]
    write("VERIFIED_SOURCE_SHA256.json",json.dumps({x:sha((ROOT/x).read_bytes()) for x in tracked},indent=2)+"\n")
    write("RESULTS.json",json.dumps({"status":"PASS","commit":git("rev-parse","HEAD").strip(),"project_specific_axioms":0,"proof_debt":0},indent=2)+"\n")

if __name__ == "__main__": main()
