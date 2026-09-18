"""Fresh C9 verification and TRUE AUDIT evidence generation."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, tempfile, zipfile

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "verification/c9"
EVIDENCE = ROOT / "audit-evidence/c9"
BASE = "7769545a357c0c4d24520ec7a9fc8994f3f664e7"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SUPPLEMENT = ROOT / "reference_inputs/P21_supplement_v1.zip"
SUPPLEMENT_SHA = "24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e"
TABLE_SHA = "9ba4fdcbdc1b5440785232e97e8cf8d729c3cf1254d87551d3a90d9abbff5916"
VERIFIER_SHA = "bcdedc3525a397601fd49704629e221f0e34e6d5ffcdc0c9c8e22d3f25775ae1"
TABLE_A = "supplement/verification_scripts/LINEAR/I_FIT_POSITIVE_COEFFICIENTS.json"
TABLE_B = "supplement/coefficient_tables/I_FIT_POSITIVE_COEFFICIENTS.json"
VERIFIER = "supplement/verification_scripts/LINEAR/verify_D_linear.py"
EXPECTED = "supplement/expected_outputs/D_LINEAR_stdout.txt"

def sha(data: bytes) -> str: return hashlib.sha256(data).hexdigest()
def write(name: str, value: str) -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / name).write_text(value, encoding="utf-8", newline="\n")
def run(cmd: list[str], log: str, append: bool = False, cwd: Path = ROOT) -> str:
    p = subprocess.run(cmd, cwd=cwd, text=True, encoding="utf-8", errors="replace",
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    with (EVIDENCE / log).open("a" if append else "w", encoding="utf-8", newline="\n") as f:
        f.write("$ " + " ".join(cmd) + "\n" + p.stdout + f"\nEXIT={p.returncode}\n")
    if p.returncode: raise RuntimeError("failed: " + " ".join(cmd))
    return p.stdout
def git(*args: str) -> str:
    return subprocess.check_output(["git", "-c", f"safe.directory={ROOT.as_posix()}", *args], cwd=ROOT).decode()

def integrity() -> None:
    frozen = json.loads((HERE / "frozen_manifest.json").read_text(encoding="utf-8"))
    if frozen["base_commit"] != BASE: raise RuntimeError("frozen base mismatch")
    bad = []
    for item in frozen["files"]:
        path = ROOT / item["path"]
        if not path.is_file() or sha(path.read_bytes()) != item["sha256"]: bad.append(item["path"])
    write("FROZEN_SOURCE_INTEGRITY.txt",
          f"Base: {BASE}\nProtected files: {len(frozen['files'])}\nSOURCE_CHANGED: {'YES' if bad else 'NO'}\n" + "\n".join(bad) + "\n")
    if bad: raise RuntimeError("frozen source changed")

def modules() -> list[str]:
    paths = sorted((ROOT / "P21/Nonsymmetric/Chain/C9").glob("*.lean"))
    paths.append(ROOT / "P21/Nonsymmetric/Chain/C9.lean")
    mods = [p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".") for p in paths]
    write("C9_MODULE_LIST.txt", "\n".join(mods) + "\n")
    return mods

def debt() -> None:
    forbidden = re.compile(r"\b(sorry|admit|axiom|sorryAx|run_tac|native_decide)\b|\bunsafe\s+(?:theorem|def)\b|\bopaque\b")
    hits = []
    paths = sorted((ROOT / "P21/Nonsymmetric/Chain/C9").glob("*.lean")) + [ROOT / "P21/Nonsymmetric/Chain/C9.lean"]
    for p in paths:
        for n, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            if forbidden.search(line.split("--", 1)[0]): hits.append(f"{p.relative_to(ROOT)}:{n}:{line}")
    write("PROOF_DEBT_REPORT.txt", "PROOF DEBT: 0\n" if not hits else "\n".join(hits) + "\n")
    if hits: raise RuntimeError("proof debt")

def dag() -> None:
    graph = {}
    for p in sorted((ROOT / "P21").rglob("*.lean")):
        mod = p.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
        graph[mod] = re.findall(r"^import\s+([\w.]+)", p.read_text(encoding="utf-8-sig"), re.M)
    active, done = set(), set()
    def visit(node: str) -> None:
        if node in active: raise RuntimeError("circular import " + node)
        if node in done: return
        active.add(node)
        for child in graph.get(node, []): visit(child)
        active.remove(node); done.add(node)
    for node in graph: visit(node)
    seen = set()
    def collect(node: str) -> None:
        if node in seen: return
        seen.add(node)
        for child in graph.get(node, []): collect(child)
    collect("P21.Nonsymmetric.Chain.C9")
    forbidden = sorted(x for x in seen if ".C10" in x or x.endswith(".Impossibility") or x.endswith(".Exclusion"))
    write("DEPENDENCY_DAG_CHECK.txt", json.dumps(graph, indent=2) + "\nIMPORT DAG: ACYCLIC\n")
    write("CIRCULARITY_CHECK.txt", "C9 imports:\n" + "\n".join(sorted(seen)) + "\nFORBIDDEN=" + repr(forbidden) + "\n")
    if forbidden: raise RuntimeError("forbidden reverse dependency")

def certificate() -> None:
    raw = SUPPLEMENT.read_bytes()
    if sha(raw) != SUPPLEMENT_SHA: raise RuntimeError("supplement SHA mismatch")
    with zipfile.ZipFile(SUPPLEMENT) as z:
        table_a, table_b, verifier, expected = z.read(TABLE_A), z.read(TABLE_B), z.read(VERIFIER), z.read(EXPECTED)
        result = json.loads(z.read("supplement/verification_scripts/LINEAR/verification_result.json"))
        if table_a != table_b or sha(table_a) != TABLE_SHA or sha(verifier) != VERIFIER_SHA:
            raise RuntimeError("certificate input mismatch")
        if result["status"] != "PASS" or result["identity_count"] != 28:
            raise RuntimeError("frozen result mismatch")
        poly = result["positive_polynomial"]
        if poly != {"monomial_count":715, "constant_term":35, "sha256":TABLE_SHA}:
            raise RuntimeError("frozen polynomial metadata mismatch")
        with tempfile.TemporaryDirectory() as d:
            z.extractall(d)
            vp = Path(d) / VERIFIER
            out = run([sys.executable, str(vp)], "LINEAR_ORIGINAL_VERIFIER_LOG.txt", cwd=vp.parent)
    if out.strip().encode() != expected.strip(): raise RuntimeError("original verifier stdout mismatch")
    write("LINEAR_SUPPLEMENT_HASHES.json", json.dumps({
        "supplement_sha256": sha(raw), "table_a_sha256": sha(table_a),
        "table_b_sha256": sha(table_b), "tables_byte_identical": table_a == table_b,
        "verifier_sha256": sha(verifier), "status": "PASS", "identity_count": 28,
        "monomial_count": 715, "constant": 35}, indent=2) + "\n")
    run([sys.executable, "verification/c9/generate_linear_certificate.py", "--check"],
        "LINEAR_CERTIFICATE_GENERATION_CHECK.txt")
    run(["lake", "build", "P21.Nonsymmetric.Chain.C9.LinearCertificate"],
        "LINEAR_CERTIFICATE_LEAN_BUILD.txt")

def regressions() -> None:
    groups = {
      "M1_ORIGINAL_SUITE.txt": ["verification/StatementCheck.lean", "verification/AxiomCheck.lean"],
      "M2A_ORIGINAL_SUITE.txt": ["verification/m2/StableCoreRegression.lean", "verification/m2/BranchIIRegression.lean"],
      "M2B_ORIGINAL_SUITE.txt": ["verification/m2b/Regression.lean"],
      "M3A_ORIGINAL_SUITE.txt": ["verification/m3/M3Regression.lean", "verification/m3/ExtractionRegression.lean"],
      "M3B1_ORIGINAL_SUITE.txt": ["verification/m3b1/StatementRegression.lean"],
      "M3B2_ORIGINAL_SUITE.txt": [str(p.relative_to(ROOT)).replace("\\", "/") for p in sorted((ROOT / "verification/m3b2").glob("*Regression.lean"))],
      "P5_ORIGINAL_SUITE.txt": ["verification/p5/StatementGate.lean", "verification/p5/Regression.lean"],
      "T6_ORIGINAL_SUITE.txt": ["verification/t6/StatementGate.lean", "verification/t6/Regression.lean"],
      "C7_ORIGINAL_SUITE.txt": ["verification/c7/StatementGate.lean", "verification/c7/Regression.lean"],
      "C8_ORIGINAL_SUITE.txt": ["verification/c8/StatementGate.lean", "verification/c8/Regression.lean"],
    }
    imports = []
    for files in groups.values():
        for f in files: imports += re.findall(r"^import\s+([\w.]+)", (ROOT / f).read_text(encoding="utf-8-sig"), re.M)
    run(["lake", "build", *sorted(set(imports))], "OLD_SUITE_BUILD_LOG.txt")
    for log, files in groups.items():
        for i, f in enumerate(files): run(["lake", "env", "lean", f], log, append=i > 0)

def evidence_manifest() -> None:
    files = sorted(p for p in EVIDENCE.iterdir() if p.is_file() and p.name != "EVIDENCE_SHA256.json")
    write("EVIDENCE_SHA256.json", json.dumps({"convention":"SHA-256 of every artifact file except this manifest",
          "files":{p.name:sha(p.read_bytes()) for p in files}}, indent=2) + "\n")

def main() -> None:
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    write("RUN_CONTEXT.json", json.dumps({"branch":git("branch", "--show-current").strip(),
          "commit":git("rev-parse", "HEAD").strip(), "github_run_id":os.getenv("GITHUB_RUN_ID"),
          "github_run_attempt":os.getenv("GITHUB_RUN_ATTEMPT")}, indent=2) + "\n")
    write("COMMIT_SHA.txt", git("rev-parse", "HEAD"))
    env = run(["lake", "--version"], "_env.tmp") + run(["lean", "--version"], "_lean.tmp")
    write("ENVIRONMENT.txt", env)
    integrity(); debt(); dag(); certificate(); mods = modules()
    run(["lake", "build"], "ROOT_BUILD_LOG.txt")
    run(["lake", "build", *mods], "C9_BUILD_LOG.txt")
    gates = sorted((ROOT / "verification/c9").glob("*Gate.lean"))
    for i, gate in enumerate(gates):
        run(["lake", "env", "lean", str(gate.relative_to(ROOT)).replace("\\", "/")],
            "C9_VERIFICATION_LOG.txt", append=i > 0)
    run(["lake", "env", "lean", "verification/c9/Regression.lean"], "C9_VERIFICATION_LOG.txt", append=True)
    run(["lake", "env", "lean", "verification/c9/StatementGate.lean"], "STATEMENT_INSPECTION.txt")
    ax = run(["lake", "env", "lean", "verification/c9/GeneratedAxiomCheck.lean"], "AXIOM_REPORT.txt")
    roots = set(re.findall(r"\b(?:propext|Classical\.choice|Quot\.sound|[A-Za-z0-9_.]+Ax)\b", ax))
    bad = roots - ALLOWED_AXIOMS
    write("AXIOM_SUMMARY.json", json.dumps({"allowed":sorted(ALLOWED_AXIOMS), "observed":sorted(roots),
          "project_specific_axioms":len(bad)}, indent=2) + "\n")
    if bad: raise RuntimeError("unexpected axioms " + repr(bad))
    regressions(); integrity(); debt(); dag()
    tracked = [x for x in git("ls-files").splitlines() if (ROOT / x).is_file()]
    write("VERIFIED_SOURCE_SHA256.json", json.dumps({x:sha((ROOT/x).read_bytes()) for x in tracked}, indent=2) + "\n")
    receipt = ROOT / "ci/C9_CANDIDATE_SHA256.txt"
    write("CANDIDATE_ZIP_SHA256.txt", receipt.read_text(encoding="utf-8") if receipt.exists() else "NOT_YET_GENERATED\n")
    write("RESULTS.json", json.dumps({"status":"PASS", "commit":git("rev-parse", "HEAD").strip(),
          "project_specific_axioms":0, "proof_debt":0, "source_changed":False}, indent=2) + "\n")
    for tmp in ("_env.tmp", "_lean.tmp"):
        p = EVIDENCE / tmp
        if p.exists(): p.unlink()
    evidence_manifest()

if __name__ == "__main__": main()
