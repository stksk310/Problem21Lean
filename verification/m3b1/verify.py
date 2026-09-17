"""M3B1 proof gates. All preexisting Lean and verification sources are immutable."""
from pathlib import Path
import argparse
import functools
import importlib.util
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "verification/m3b1"
EVIDENCE = ROOT / "audit-evidence/m3b1"
FROZEN = "258d74ac941796c62bb45cc177f22a7396319413"
PREFIX_FILE = "verification/m3/local-evidence/KERNEL_DECLARATION_PREFIX.txt"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


V = load("m3b1_frozen_helpers", ROOT / "verification/m2b/verify.py")
V.EVIDENCE = EVIDENCE
sha, write, record, run, lake = V.sha, V.write, V.record, V.run, V.lake


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def protect_path(p):
    return (p.endswith(".lean") or p.startswith("verification/")
            or (p.startswith("ci/candidate/") and p.endswith(".zip"))
            or (p.startswith("ci/") and p.endswith("_SHA256.txt"))
            or (p.startswith("ci/") and p.endswith((".py", ".ps1")))
            or p in {"lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json"})


@functools.lru_cache(maxsize=1)
def git_protected():
    names = git("ls-tree", "-r", "--name-only", FROZEN).decode("utf-8").splitlines()
    chosen = sorted(p for p in names if protect_path(p))
    # One batch Git process; never trust an editable list as baseline authority.
    payload = "".join(FROZEN + ":" + p + "\n" for p in chosen).encode("utf-8")
    raw = subprocess.check_output(["git", "cat-file", "--batch"], input=payload, cwd=ROOT)
    data, pos = {}, 0
    for p in chosen:
        end = raw.index(b"\n", pos)
        header = raw[pos:end].split()
        if len(header) != 3 or header[1] != b"blob":
            raise ValueError("Missing frozen Git blob: " + p)
        size = int(header[2]); pos = end + 1
        data[p] = raw[pos:pos+size]; pos += size + 1
    if pos != len(raw): raise ValueError("Unexpected Git batch trailing data")
    if sum(p.endswith(".lean") for p in data) != 96:
        raise ValueError("Expected exact baseline with 96 project-owned Lean files")
    return data


def freeze_manifest():
    path = HERE / "FROZEN_SHA256.json"
    text = json.dumps(dict(commit=FROZEN, files={p:sha(b) for p,b in git_protected().items()}), indent=2)+"\n"
    if path.exists() and path.read_text(encoding="utf-8") != text:
        raise ValueError("Existing M3B1 frozen manifest differs from Git")
    path.write_text(text, encoding="utf-8", newline="\n")


def protected():
    obj = json.loads((HERE / "FROZEN_SHA256.json").read_text(encoding="utf-8"))
    expected = {p:sha(b) for p,b in git_protected().items()}
    if obj.get("commit") != FROZEN or obj.get("files") != expected:
        raise ValueError("Frozen manifest differs from exact Git baseline")
    return expected


def integrity():
    hashes = protected()
    bad = [p for p,h in hashes.items() if not (ROOT/p).is_file() or sha((ROOT/p).read_bytes()) != h]
    write("FROZEN_SOURCE_INTEGRITY_REPORT_M3B1.txt", f"Base: {FROZEN}\nProtected: {len(hashes)}\n"
          + ("FROZEN_SOURCE_CHANGED: NO\n" if not bad else "FROZEN_SOURCE_CHANGED: YES\n"+"\n".join(bad)))
    if bad: raise ValueError("Frozen source changed: " + repr(bad))
    record("frozen_integrity", "PASS")
    record("frozen_lean_files", 96)
    record("frozen_protected_files", len(hashes))


def modules():
    old = git_protected()
    return [p for p in sorted((ROOT/"P21").rglob("*.lean")) if p.relative_to(ROOT).as_posix() not in old]


def name(p): return p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def source_files():
    names=git('ls-files','--cached','--others','--exclude-standard','-z').decode().split('\0')
    return sorted({n for n in names if n and (Path(n).suffix in {'.lean','.py','.ps1','.yml','.yaml'}
        or Path(n).name in {'lean-toolchain','lakefile.toml','lake-manifest.json'}
        or n in {'verification/m3b1/MILESTONE.json','verification/m3b1/FROZEN_SHA256.json'})})


def source_snapshot():
    return {n:sha((ROOT/n).read_bytes()) for n in source_files()}


def milestone():
    data = json.loads((HERE/"MILESTONE.json").read_text(encoding="utf-8"))
    required = {"candidate", "status", "minimum_one_proved", "std_white", "required_theorems", "statement_regression"}
    if not required <= data.keys(): raise ValueError("Incomplete MILESTONE.json schema")
    if type(data["minimum_one_proved"]) is not bool: raise ValueError("minimum_one_proved must be Boolean")
    if data["std_white"] not in {"OPEN", "PROVED"}: raise ValueError("Invalid STD_WHITE status")
    if not isinstance(data["required_theorems"], list) or not data["required_theorems"]:
        raise ValueError("Milestone must name proved theorem roots")
    for n in data["required_theorems"]:
        if not re.fullmatch(r"P21\.[A-Za-z_0-9.]+", n): raise ValueError("Invalid theorem name")
    archive = data["candidate"]
    if Path(archive).name != archive or not archive.endswith(".zip") or not archive.startswith("P21_LEAN_M3B1"):
        raise ValueError("Invalid candidate ZIP basename")
    reg = Path(data["statement_regression"])
    if reg.as_posix().startswith("verification/m3b1/") is False or ".." in reg.parts or reg.suffix != ".lean":
        raise ValueError("Regression must be a new M3B1 Lean file")
    if data["minimum_one_proved"] and not re.fullmatch(r"P21\.[A-Za-z_0-9.]+", data.get("minimum_one_theorem", "")):
        raise ValueError("Full success must name its exact MinimumOne proof")
    if data["minimum_one_proved"] and data["minimum_one_theorem"] not in data["required_theorems"]:
        raise ValueError("Exact MinimumOne proof must also be a required new theorem root")
    return data


def generate(require_milestone=True):
    paths = modules()
    if not paths: raise ValueError("No new M3B1 modules")
    rows = [r for p in paths for r in V.inventory_source(
        re.sub(r"(?m)^(@\[[^\]]+\]\s*)+", lambda m: "\n"*m[0].count("\n"), p.read_text(encoding="utf-8-sig")),
        p.relative_to(ROOT).as_posix())]
    for p in paths:
        code = V.SCANNER.code_only(p.read_text(encoding="utf-8-sig"))
        if re.search(r"\bprivate\s+(?:theorem|lemma|def|abbrev|instance)\b", code):
            raise ValueError("Private declarations are outside the explicit kernel namespace contract: " + str(p))
    names = [r["name"] for r in rows]
    if len(names) != len(set(names)): raise ValueError("Duplicate explicit declarations")
    if any(not n.startswith("P21.Nonsymmetric.") for n in names):
        raise ValueError("New declarations outside inventoried namespace")
    old = sorted(p[:-5].replace("/", ".") for p in git_protected() if p.startswith("P21/Nonsymmetric/") and p.endswith(".lean"))
    imports = "".join("import " + n + "\n" for n in old + list(map(name, paths)))
    enum = """-- Read-only inventory; no theorem or proof is created.
run_cmd do
  for (n, _) in (← Lean.getEnv).constants do
    if n.toString.startsWith "P21.Nonsymmetric." then
      Lean.logInfo (Lean.MessageData.ofName n)
"""
    (HERE/"PrefixCheck.lean").write_text(imports+enum, encoding="utf-8", newline="\n")
    checks = "\n".join("#check " + n for n in names)+"\n"
    if require_milestone:
        status = milestone()
        missing = set(status["required_theorems"])-set(names)
        if missing: raise ValueError("Milestone theorem absent from new sources: " + repr(missing))
        checks += "\n".join("#check "+n for n in status["required_theorems"])+"\n"
        if status["minimum_one_proved"]:
            checks += "example : P21.Nonsymmetric.ColorCap.MinimumOneStatement := " + status["minimum_one_theorem"]+"\n"
    checks += "#print P21.Nonsymmetric.ColorCap.MinimumOneStatement\n#print P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement\n"
    (HERE/"GeneratedStatementCheck.lean").write_text(imports+checks, encoding="utf-8", newline="\n")
    (HERE/"DECLARATIONS.json").write_text(json.dumps(rows,indent=2,ensure_ascii=False)+"\n",encoding="utf-8",newline="\n")
    write("M3B1_MODULE_LIST.txt", "\n".join(map(name,paths))+"\n")
    record("m3b1_module_count",len(paths))
    return paths, rows, imports


def prefix_names(text):
    return {n.rstrip(".") for n in re.findall(r"P21\.Nonsymmetric[\w.\u0080-\uffff']*",text)
            if n != "P21.Nonsymmetric"}


def axioms(rows, imports):
    frozen_text = git_protected()[PREFIX_FILE].decode("utf-8")
    frozen_roots = prefix_names(frozen_text)
    if len(frozen_roots) != 1327: raise ValueError("Frozen kernel prefix must contain 1327 declarations")
    run(lake()+["env","lean","verification/m3b1/PrefixCheck.lean"],"KERNEL_DECLARATION_PREFIX.txt")
    all_roots = prefix_names((EVIDENCE/"KERNEL_DECLARATION_PREFIX.txt").read_text(encoding="utf-8"))
    # All baseline modules are imported by PrefixCheck below, preventing accidental omission.
    if not frozen_roots <= all_roots: raise ValueError("Missing frozen namespace declarations")
    roots = sorted(all_roots-frozen_roots)
    explicit = {r["name"] for r in rows}
    if not explicit <= set(roots): raise ValueError("New explicit declarations missing from kernel delta: "+repr(explicit-set(roots)))
    if not roots: raise ValueError("Empty new kernel inventory")
    (HERE/"GeneratedAxiomCheck.lean").write_text(imports+"\nset_option linter.auxLemma false\n"+
        "\n".join("#print axioms "+n for n in roots)+"\n",encoding="utf-8",newline="\n")
    run(lake()+["env","lean","verification/m3b1/GeneratedAxiomCheck.lean"],"AXIOM_REPORT_M3B1.txt")
    found = V.parse_axioms((EVIDENCE/"AXIOM_REPORT_M3B1.txt").read_text(encoding="utf-8"),roots)
    write("AXIOM_SUMMARY.json",json.dumps(dict(frozen_declarations=len(frozen_roots),checked_declarations=len(found),
        project_specific_axioms=0,declarations=found),indent=2)+"\n")
    record("project_specific_axioms",0); record("axiom_roots",len(found)); record("frozen_axiom_roots",1327)
    record("kernel_inventory", "PASS")


def dag():
    graph = {}
    for p in [ROOT/"P21.lean"]+sorted((ROOT/"P21").rglob("*.lean")):
        code=V.SCANNER.code_only(p.read_text(encoding="utf-8-sig"))
        graph[name(p)]=re.findall(r"^import\s+([\w.]+)",code,re.M)
    active,done=set(),set()
    def visit(n):
        if n in active: raise ValueError("Circular import: "+n)
        if n in done: return
        active.add(n)
        for child in graph.get(n,[]): visit(child)
        active.remove(n); done.add(n)
    for n in graph:visit(n)
    write("DEPENDENCY_DAG_CHECK.txt",json.dumps(graph,indent=2)+"\nACYCLIC\n")
    write("CIRCULARITY_CHECK.txt","Full project import graph acyclic; exact frozen byte gate prevents backwards dependency edits.\n")
    record("dependency_dag","PASS")


def debt():
    V.debt()
    source=EVIDENCE/"PROOF_DEBT_REPORT.txt"
    write("PROOF_DEBT_REPORT_M3B1.txt",source.read_text(encoding="utf-8"))


def preflight():
    freeze_manifest(); integrity(); paths,rows,imports=generate(False); debt(); dag()
    record("kernel_inventory", "PENDING_VERIFICATION")
    record("m3b1_preflight","PASS")
    return paths,rows,imports


def verify(fresh=False):
    record('m3b1_verification_exit_code',None)
    record('verified_source_integrity','PENDING')
    integrity()
    paths,rows,imports=generate()
    generated_axioms='verification/m3b1/GeneratedAxiomCheck.lean'
    before={n:h for n,h in source_snapshot().items() if n!=generated_axioms}
    debt()
    if fresh and any((ROOT/".lake/build").rglob("*.olean")): raise ValueError("Fresh requires no project oleans")
    record("fresh_root_build",fresh)
    run(lake()+["build"],"ROOT_BUILD_LOG.txt")
    frozen=sorted(p[:-5].replace("/",".") for p in protected() if p.startswith("P21/") and p.endswith(".lean"))
    run(lake()+["build"]+frozen,"FROZEN_BUILD_LOG.txt")
    run(lake()+["build"]+list(map(name,paths)),"BUILD_LOG_M3B1.txt")
    axioms(rows,imports)
    run(lake()+["env","lean","verification/m3b1/GeneratedStatementCheck.lean"],"STATEMENT_INSPECTION.txt")
    status=milestone()
    reg=ROOT/status["statement_regression"]
    if not reg.is_file(): raise ValueError("Exact statement regression missing")
    run(lake()+["env","lean",str(reg.relative_to(ROOT))],"REGRESSION_REPORT_M3B1.txt")
    for directory,pattern in [("verification/m2","test_debt_scan.py"),("verification/m2b","test_*.py"),("ci","test_*.py"),("verification/m3b1","test_*.py")]:
        run([sys.executable,"-m","unittest","discover","-s",directory,"-p",pattern,"-v"],"SCANNER_TEST_LOG.txt",append=directory!="verification/m2")
    dag(); debt(); integrity()
    after=source_snapshot()
    if before!={n:h for n,h in after.items() if n!=generated_axioms}:
        raise ValueError('Executable source changed during verification')
    write('VERIFIED_SOURCE_SHA256.json',json.dumps(after,indent=2)+'\n')
    record('verified_source_integrity','PASS')
    for key in ["minimum_one_proved","std_white","status"]: record(key,status[key])
    record("remaining_frontier",["BoxPositiveExitStatement"] if status["minimum_one_proved"] else ["MinimumOneStatement","BoxPositiveExitStatement"])
    record("m3b1_verification_exit_code",0)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--generate",action="store_true")
    parser.add_argument("--preflight",action="store_true")
    parser.add_argument("--fresh",action="store_true")
    parser.add_argument("--local-fresh-evidence",action="store_true")
    args=parser.parse_args()
    if args.local_fresh_evidence:
        EVIDENCE=ROOT/'audit-evidence/m3b1-local-fresh'
        V.EVIDENCE=EVIDENCE
    if args.preflight: preflight()
    elif args.generate: freeze_manifest(); generate()
    else: verify(args.fresh)
