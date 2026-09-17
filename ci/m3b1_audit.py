"""Exact-source M3B1 CI and four unchanged isolated historical suites."""
from pathlib import Path
import importlib.util
import json
import os
import platform
import re
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec); spec.loader.exec_module(obj); return obj
V=load("m3b1_verifier",ROOT/"verification/m3b1/verify.py")
OLD=load("m3b1_archive_reader",ROOT/"ci/m2b_audit.py")
REQUIRED="""COMMIT_SHA.txt RUN_CONTEXT.json ENVIRONMENT.txt FROZEN_SOURCE_INTEGRITY_REPORT_M3B1.txt
CANDIDATE_SOURCE_INTEGRITY.txt DEPENDENCY_STATE.txt ROOT_BUILD_LOG.txt FROZEN_BUILD_LOG.txt
BUILD_LOG_M3B1.txt M3B1_MODULE_LIST.txt AXIOM_REPORT_M3B1.txt AXIOM_SUMMARY.json STATEMENT_INSPECTION.txt
PROOF_DEBT_REPORT_M3B1.txt DEPENDENCY_DAG_CHECK.txt REGRESSION_REPORT_M3B1.txt SCANNER_TEST_LOG.txt
M1_ORIGINAL_SUITE.txt M2A_ORIGINAL_SUITE.txt M2B_ORIGINAL_SUITE.txt M3A_ORIGINAL_SUITE.txt OLD_SUITE_LOG.txt
M3B1_VERIFICATION_LOG.txt CIRCULARITY_CHECK.txt KERNEL_DECLARATION_PREFIX.txt VERIFIED_SOURCE_SHA256.json RESULTS.json""".split()
git=V.git


def init():
    V.EVIDENCE.mkdir(parents=True,exist_ok=True)
    for n in REQUIRED: V.write(n,"NOT RUN\n")
    V.write("RESULTS.json","{}\n")
    head=git("rev-parse","HEAD").decode("utf-8").strip()
    if os.environ.get("GITHUB_SHA",head)!=head: raise ValueError("Event/HEAD mismatch")
    V.write("COMMIT_SHA.txt",head+"\n")
    V.write("RUN_CONTEXT.json",json.dumps({k:os.environ.get(k) for k in
      ["GITHUB_REPOSITORY","GITHUB_SHA","GITHUB_REF","GITHUB_RUN_ID","GITHUB_RUN_ATTEMPT","GITHUB_WORKFLOW","RUNNER_OS","RUNNER_ARCH"]},indent=2)+"\n")


def baseline():
    status=V.milestone()
    path=ROOT/"ci/candidate"/status["candidate"]
    receipt=(ROOT/"ci/M3B1_CANDIDATE_SHA256.txt").read_text(encoding="utf-8").split()
    if not receipt or not re.fullmatch("[0-9a-f]{64}",receipt[0]): raise ValueError("Malformed candidate digest")
    if len(receipt)>1 and Path(receipt[1]).name!=path.name: raise ValueError("Receipt archive name mismatch")
    return path,OLD.archive_data(path,receipt[0])


def integrity():
    V.integrity()
    archive,data=baseline()
    tracked=set(git("ls-files","-z").decode("utf-8").rstrip("\0").split("\0"))
    frozen=V.protected()
    def source(p):
        return (p.endswith((".lean",".py",".ps1",".yml",".yaml")) or p in frozen
                or (p.startswith("verification/m3b1/") and p.endswith(".json")))
    cs,gs={p for p in data if source(p)},{p for p in tracked if source(p)}
    if cs!=gs: raise ValueError("ZIP/Git source inventory mismatch: "+repr(cs^gs))
    for p in cs:
        if data[p]!=(ROOT/p).read_bytes() or data[p]!=git("show","HEAD:"+p):
            raise ValueError("ZIP/Git/workspace byte mismatch: "+p)
    if any(".lake" in Path(p).parts or p.endswith((".olean",".ilean",".o",".so")) for p in tracked):
        raise ValueError("Tracked build artifact")
    V.write("CANDIDATE_SOURCE_INTEGRITY.txt",f"Candidate: {archive.name}\nSHA256: {V.sha(archive.read_bytes())}\nExact source files: {len(cs)}\nSOURCE_CHANGED: NO\n")
    V.record("candidate_source_integrity","PASS")
    V.record("candidate_zip_sha256",V.sha(archive.read_bytes()))


def environment():
    V.write("ENVIRONMENT.txt",platform.platform()+"\nPython "+sys.version+"\n")
    for args in [V.lake()+["--version"],V.lake()+["env","lean","--version"],["git","--version"]]:
        V.run(args,"ENVIRONMENT.txt",append=True)


def windows_environment():
    if os.name!="nt":return
    elan=Path(os.environ.get("ELAN_HOME","C:/Users/stksk/.elan"))
    toolchain=(ROOT/"lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---")
    bindir=elan/"toolchains"/toolchain/"bin"
    if not (bindir/"lake.exe").is_file():raise ValueError("Pinned Windows lake missing")
    os.environ["ELAN_HOME"]=str(elan)
    os.environ["PATH"]=str(bindir)+os.pathsep+os.environ["PATH"]
    packages=sorted(p for p in (ROOT/".lake/packages").resolve().iterdir() if p.is_dir() and (p/".git").exists())
    os.environ["GIT_CONFIG_COUNT"]=str(len(packages))
    for i,p in enumerate(packages):
        os.environ[f"GIT_CONFIG_KEY_{i}"]="safe.directory"
        os.environ[f"GIT_CONFIG_VALUE_{i}"]=p.as_posix()


def dependencies():
    windows_environment()
    manifest=json.loads((ROOT/"lake-manifest.json").read_text(encoding="utf-8-sig"))
    lines=[]
    for pkg in manifest["packages"]:
        path=ROOT/manifest["packagesDir"]/pkg["name"]
        rev=subprocess.check_output(["git","-C",str(path),"rev-parse","HEAD"],text=True,encoding="utf-8").strip()
        dirty=subprocess.check_output(["git","-C",str(path),"status","--porcelain","--untracked-files=no"],text=True,encoding="utf-8")
        if rev!=pkg["rev"] or dirty:raise ValueError("Dependency source mismatch: "+pkg["name"])
        lines.append(f"{pkg['name']} {rev} {pkg['url']}")
    V.write("DEPENDENCY_STATE.txt","\n".join(lines)+"\nALL PINNED REVISIONS MATCH\n")
    V.record("pinned_dependencies",len(lines))


def cache_modules():
    imports=set()
    for p in V.V.lean_files():
        imports.update(re.findall(r"^import (Mathlib\.[\w.]+)",p.read_text(encoding="utf-8-sig"),re.M))
    print("\n".join(sorted(imports)))


def suite():
    windows_environment()
    # Do not reuse old CI write/record globals: their evidence roots belong to old milestones.
    sys.path.insert(0,str(ROOT/"ci"))
    m1=load("m3b1_m1_archive",ROOT/"ci/audit.py")
    m2a=load("m3b1_m2a_archive",ROOT/"ci/m2a_audit.py")
    m3archive=ROOT/"ci/candidate/P21_LEAN_M3A_NONSYMMETRIC_LOCAL_GEOMETRY_CANDIDATE_20260917.zip"
    m3digest=(ROOT/"ci/M3_CANDIDATE_SHA256.txt").read_text(encoding="utf-8").split()[0]
    archives=[("M1",m1.baseline(),"verification/verify.py"),
              ("M2A",m2a.baseline(),"verification/m2/verify.py"),
              ("M2B",OLD.baseline(),"verification/m2b/verify.py"),
              ("M3A",OLD.archive_data(m3archive,m3digest),"verification/m3/verify.py")]
    for label,data,script in archives:
        with tempfile.TemporaryDirectory(prefix="isolated-"+label+"-",dir=V.EVIDENCE) as tmp:
            scratch=Path(tmp).resolve()
            if not scratch.is_relative_to(V.EVIDENCE.resolve()):raise ValueError("Invalid scratch root")
            for n,b in data.items():
                p=scratch/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
            (scratch/".lake").mkdir()
            link=scratch/".lake/packages";deps=(ROOT/".lake/packages").resolve()
            if os.name=="nt":
                command="New-Item -ItemType Junction -Path '"+str(link).replace("'","''")+"' -Target '"+str(deps).replace("'","''")+"' | Out-Null"
                subprocess.run(["pwsh","-NoProfile","-Command",command],check=True)
            else:link.symlink_to(deps,target_is_directory=True)
            log=label+"_ORIGINAL_SUITE.txt"
            try:
                if any((scratch/".lake/build").rglob("*.olean")):raise ValueError("Historical project cache present")
                V.run([sys.executable,script],log,cwd=scratch)
                if label=="M1":
                    V.run([sys.executable,"verification/package_candidate.py","--stage"],log,cwd=scratch,append=True)
                    V.run([sys.executable,"verification/package_candidate.py"],log,cwd=scratch,append=True)
                for n,b in data.items():
                    if n.startswith("P21") and n.endswith(".lean") and (scratch/n).read_bytes()!=b:
                        raise ValueError("Historical suite changed mathematical source: "+n)
                # Preserve nested evidence before disposing of the isolated source tree.
                dest=V.EVIDENCE/"historical"/label
                import shutil
                for sub in [scratch/"audit-evidence",scratch/"verification/m2/reports"]:
                    if sub.is_dir():shutil.copytree(sub,dest/sub.name,dirs_exist_ok=True)
            finally:
                if os.name=="nt":os.rmdir(link)
                else:link.unlink()
        V.record("original_"+label.lower()+"_suite",0)
    V.write("OLD_SUITE_LOG.txt","\n".join("## "+label+" unchanged original suite\n"+
      (V.EVIDENCE/(label+"_ORIGINAL_SUITE.txt")).read_text(encoding="utf-8") for label in ["M1","M2A","M2B","M3A"]))


def verify():
    V.run([sys.executable,"verification/m3b1/verify.py","--fresh"],"M3B1_VERIFICATION_LOG.txt")


def verify_local():
    # Independent local suites may run concurrently; their result maps never race.
    V.EVIDENCE=ROOT/'audit-evidence/m3b1-local-fresh'
    V.V.EVIDENCE=V.EVIDENCE
    V.run([sys.executable,'verification/m3b1/verify.py','--fresh','--local-fresh-evidence'],'M3B1_VERIFICATION_LOG.txt')


def complete():
    for n in REQUIRED:
        p=V.EVIDENCE/n
        if not p.is_file() or not p.stat().st_size or p.read_text(encoding="utf-8").startswith("NOT RUN"):
            raise ValueError("Missing evidence: "+n)
    result=json.loads((V.EVIDENCE/"RESULTS.json").read_text(encoding="utf-8"))
    status=V.milestone()
    expected=dict(frozen_integrity="PASS",frozen_lean_files=96,candidate_source_integrity="PASS",fresh_root_build=True,
      proof_debt_tokens=0,project_specific_axioms=0,m3b1_verification_exit_code=0,dependency_dag="PASS",
      original_m1_suite=0,original_m2a_suite=0,original_m2b_suite=0,original_m3a_suite=0,frozen_axiom_roots=1327,kernel_inventory="PASS",
      minimum_one_proved=status["minimum_one_proved"],std_white=status["std_white"],status=status["status"],verified_source_integrity="PASS")
    for k,v in expected.items():
        if result.get(k)!=v:raise ValueError("Failed evidence gate: "+k)
    if not result.get("pinned_dependencies") or not result.get("axiom_roots") or not result.get("m3b1_module_count"):
        raise ValueError("Empty dependency/declaration/module coverage")
    V.record("all_required_checks_passed",True)
    V.write("EVIDENCE_SHA256.json",json.dumps({p.relative_to(V.EVIDENCE).as_posix():V.sha(p.read_bytes())
       for p in sorted(V.EVIDENCE.rglob("*")) if p.is_file() and p != V.EVIDENCE/"EVIDENCE_SHA256.json"},indent=2)+"\n")


if __name__=="__main__":
    {"init":init,"integrity":integrity,"environment":environment,"dependencies":dependencies,
     "cache-modules":cache_modules,"suite":suite,"verify":verify,"verify-local":verify_local,"complete":complete}[sys.argv[1]]()
