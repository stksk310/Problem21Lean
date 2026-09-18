"""M3B2 CI orchestration and isolated historical regression suites."""
from pathlib import Path
import importlib.util
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module); return module


V = load("m3b2_verifier", ROOT / "verification/m3b2/verify.py")
OLD = load("m3b2_archive_reader", ROOT / "ci/m2b_audit.py")
EVIDENCE = ROOT / "audit-evidence/m3b2"
REQUIRED = """COMMIT_SHA.txt RUN_CONTEXT.json ENVIRONMENT.txt DEPENDENCY_STATE.txt
FROZEN_SOURCE_INTEGRITY.txt ROOT_BUILD_LOG.txt M3B2_BUILD_LOG.txt M3B2_MODULE_LIST.txt
M3B2_VERIFICATION_LOG.txt PROOF_DEBT_REPORT_M3B2.txt AXIOM_REPORT_M3B2.txt AXIOM_SUMMARY.json
STATEMENT_INSPECTION.txt DEPENDENCY_DAG_CHECK.txt CIRCULARITY_CHECK.txt SCANNER_TEST_LOG.txt
M1_ORIGINAL_SUITE.txt M2A_ORIGINAL_SUITE.txt M2B_ORIGINAL_SUITE.txt M3A_ORIGINAL_SUITE.txt
M3B1_ORIGINAL_SUITE.txt VERIFIED_SOURCE_SHA256.json CANDIDATE_ZIP_SHA256.txt RESULTS.json""".split()


def git(*args): return subprocess.check_output(["git", *args], cwd=ROOT)


def init():
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    # RESULTS.json is shared mutable state for every audit stage, so it must be
    # valid JSON even on a completely clean runner.
    if not (EVIDENCE / "RESULTS.json").exists(): V.write("RESULTS.json", "{}\n")
    for name in REQUIRED:
        if name == "RESULTS.json": continue
        if not (EVIDENCE / name).exists(): V.write(name, "NOT RUN\n")
    head = git("rev-parse", "HEAD").decode().strip()
    if os.environ.get("GITHUB_SHA", head) != head: raise ValueError("Event/HEAD mismatch")
    V.write("COMMIT_SHA.txt", head + "\n")
    V.write("RUN_CONTEXT.json", json.dumps({k: os.environ.get(k) for k in
      ["GITHUB_REPOSITORY", "GITHUB_SHA", "GITHUB_REF", "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT",
       "GITHUB_WORKFLOW", "RUNNER_OS", "RUNNER_ARCH"]}, indent=2) + "\n")


def environment():
    V.write("ENVIRONMENT.txt", platform.platform() + "\nPython " + sys.version + "\n")
    for args in [V.lake() + ["--version"], V.lake() + ["env", "lean", "--version"], ["git", "--version"]]:
        V.run(args, "ENVIRONMENT.txt", append=True)


def windows_environment():
    if os.name != "nt": return
    elan = Path(os.environ.get("ELAN_HOME", "C:/Users/stksk/.elan"))
    toolchain = (ROOT / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    bindir = elan / "toolchains" / toolchain / "bin"
    if not (bindir / "lake.exe").is_file(): raise ValueError("Pinned Windows lake missing")
    os.environ["ELAN_HOME"] = str(elan); os.environ["PATH"] = str(bindir) + os.pathsep + os.environ["PATH"]
    packages = sorted(p for p in (ROOT / ".lake/packages").resolve().iterdir() if p.is_dir() and (p / ".git").exists())
    os.environ["GIT_CONFIG_COUNT"] = str(len(packages))
    for i, p in enumerate(packages):
        os.environ[f"GIT_CONFIG_KEY_{i}"] = "safe.directory"; os.environ[f"GIT_CONFIG_VALUE_{i}"] = p.as_posix()


def dependencies():
    windows_environment()
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8-sig"))
    lines = []
    for pkg in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / pkg["name"]
        rev = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"], text=True)
        if rev != pkg["rev"] or dirty: raise ValueError("Dependency mismatch: " + pkg["name"])
        lines.append(f"{pkg['name']} {rev} {pkg['url']}")
    V.write("DEPENDENCY_STATE.txt", "\n".join(lines) + "\nALL PINNED REVISIONS MATCH\n")
    V.record("pinned_dependencies", len(lines))


def cache_modules():
    imports = set()
    for p in [ROOT / "P21.lean"] + sorted((ROOT / "P21").rglob("*.lean")):
        imports.update(re.findall(r"^import (Mathlib\.[\w.]+)", p.read_text(encoding="utf-8-sig"), re.M))
    print("\n".join(sorted(imports)))


def verify():
    V.run([sys.executable, "verification/m3b2/verify.py", "--fresh"], "CI_M3B2_DRIVER.txt")


def archive(path, receipt):
    digest = receipt.read_text(encoding="utf-8").split()[0]
    return OLD.archive_data(path, digest)


def suite(selected=None):
    windows_environment()
    sys.path.insert(0, str(ROOT / "ci"))
    m1 = load("m3b2_m1_archive", ROOT / "ci/audit.py")
    m2a = load("m3b2_m2a_archive", ROOT / "ci/m2a_audit.py")
    archives = [
      ("M1", m1.baseline(), "verification/verify.py"),
      ("M2A", m2a.baseline(), "verification/m2/verify.py"),
      ("M2B", OLD.baseline(), "verification/m2b/verify.py"),
      ("M3A", archive(ROOT / "ci/candidate/P21_LEAN_M3A_NONSYMMETRIC_LOCAL_GEOMETRY_CANDIDATE_20260917.zip",
                      ROOT / "ci/M3_CANDIDATE_SHA256.txt"), "verification/m3/verify.py"),
      ("M3B1", archive(ROOT / "ci/candidate/P21_LEAN_M3B1_MINBOX_WHITE_CANDIDATE_20260917.zip",
                       ROOT / "ci/M3B1_CANDIDATE_SHA256.txt"), "verification/m3b1/verify.py")]
    for label, data, script in archives:
        if selected is not None and label != selected: continue
        with tempfile.TemporaryDirectory(prefix="isolated-" + label + "-", dir=EVIDENCE) as temp:
            container = Path(temp).resolve()
            if not container.is_relative_to(EVIDENCE.resolve()): raise ValueError("Invalid scratch path")
            worktree_added = label == "M3B1"
            if worktree_added:
                scratch = container / "checkout"
                subprocess.run(["git", "worktree", "add", "--detach", str(scratch),
                                "9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1"], cwd=ROOT, check=True)
            else:
                scratch = container
                for name, blob in data.items():
                    p = scratch / name; p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(blob)
            (scratch / ".lake").mkdir(); link = scratch / ".lake/packages"; deps = (ROOT / ".lake/packages").resolve()
            if os.name == "nt":
                command = "New-Item -ItemType Junction -Path '" + str(link).replace("'", "''") + "' -Target '" + str(deps).replace("'", "''") + "' | Out-Null"
                subprocess.run(["pwsh", "-NoProfile", "-Command", command], check=True)
            else: link.symlink_to(deps, target_is_directory=True)
            try:
                args = [sys.executable, script]
                if label in {"M3A", "M3B1"}: args.append("--fresh")
                V.run(args, label + "_ORIGINAL_SUITE.txt", cwd=scratch)
            finally:
                if os.name == "nt": os.rmdir(link)
                else: link.unlink()
                if worktree_added:
                    subprocess.run(["git", "worktree", "remove", "--force", str(scratch)], cwd=ROOT, check=True)
        V.record("original_" + label.lower() + "_suite", 0)


def integrity(): V.integrity()


def candidate():
    name = "P21_LEAN_M3B2_DPE_BOX_POSITIVE_EXIT_CANDIDATE_20260917.zip"
    path = ROOT / "ci/candidate" / name
    receipt = ROOT / "ci/M3B2_CANDIDATE_SHA256.txt"
    fields = receipt.read_text(encoding="utf-8").split()
    if len(fields) < 2 or fields[1] != name or not re.fullmatch(r"[0-9a-f]{64}", fields[0]):
        raise ValueError("Malformed M3B2 candidate receipt")
    digest = V.sha(path.read_bytes())
    if digest != fields[0]: raise ValueError("M3B2 candidate SHA mismatch")
    with zipfile.ZipFile(path) as zf:
        names = set(zf.namelist())
        required = {"README_M3B2.md", "SOURCE_OF_TRUTH_M3B2.md", "M3B2_STATEMENT_MAP.md",
                    "M3B2_PROOF_ROUTE.md", "M3B2_DEPENDENCY_DAG.md", "NEXT_RESTART.md",
                    "P21/Nonsymmetric/ColorCap/DPE/Exhaustion.lean",
                    "P21/Nonsymmetric/ColorCap/FullColorCap.lean",
                    "verification/m3b2/local-evidence/RESULTS.json"}
        if not required <= names: raise ValueError("Candidate archive missing required files")
    V.write("CANDIDATE_ZIP_SHA256.txt", digest + "  " + name + "\n")
    V.record("candidate_zip_sha256", digest)


def complete():
    for name in REQUIRED:
        path = EVIDENCE / name
        if not path.is_file() or not path.stat().st_size or path.read_text(encoding="utf-8").startswith("NOT RUN"):
            raise ValueError("Missing evidence: " + name)
    result = json.loads((EVIDENCE / "RESULTS.json").read_text(encoding="utf-8"))
    expected = {"frozen_source_integrity": "87/87", "source_changed": False,
                "fresh_root_build": True, "proof_debt_tokens": 0,
                "project_specific_axioms": 0, "dependency_dag": "PASS",
                "dpe_circularity": "PASS", "verified_source_integrity": "PASS",
                "m3b2_verification_exit_code": 0,
                "original_m1_suite": 0, "original_m2a_suite": 0, "original_m2b_suite": 0,
                "original_m3a_suite": 0, "original_m3b1_suite": 0}
    for key, value in expected.items():
        if result.get(key) != value: raise ValueError(f"Failed evidence gate: {key}")
    if not result.get("pinned_dependencies") or not result.get("axiom_roots") or not result.get("m3b2_module_count"):
        raise ValueError("Empty audit coverage")
    V.record("all_required_checks_passed", True)
    V.write("EVIDENCE_SHA256.json", json.dumps({p.relative_to(EVIDENCE).as_posix(): V.sha(p.read_bytes())
      for p in sorted(EVIDENCE.rglob("*")) if p.is_file() and p.name != "EVIDENCE_SHA256.json"}, indent=2) + "\n")


if __name__ == "__main__":
    {"init": init, "environment": environment, "dependencies": dependencies,
     "cache-modules": cache_modules, "verify": verify, "suite": suite,
     "suite-m3b1": lambda: suite("M3B1"),
     "integrity": integrity, "candidate": candidate, "complete": complete}[sys.argv[1]]()
