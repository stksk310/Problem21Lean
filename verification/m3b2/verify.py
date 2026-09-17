"""M3B2 DPE, residual-free integration, and immutable-source verification."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "verification/m3b2"
EVIDENCE = ROOT / "audit-evidence/m3b2"
BASE = "9c9a1b6f76f78a2927b12bf8a0663dfdc29ea7a1"


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


V = load("m3b2_frozen_helpers", ROOT / "verification/m2b/verify.py")
V.EVIDENCE = EVIDENCE
sha, write, record, run, lake = V.sha, V.write, V.record, V.run, V.lake


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def baseline_lean():
    names = [p for p in git("ls-tree", "-r", "--name-only", BASE, "P21").decode().splitlines()
             if p.endswith(".lean")]
    if len(names) != 87:
        raise ValueError(f"Expected 87 protected mathematical Lean files, found {len(names)}")
    payload = "".join(BASE + ":" + p + "\n" for p in names).encode()
    raw = subprocess.check_output(["git", "cat-file", "--batch"], input=payload, cwd=ROOT)
    data, pos = {}, 0
    for p in names:
        end = raw.index(b"\n", pos)
        header = raw[pos:end].split()
        if len(header) != 3 or header[1] != b"blob":
            raise ValueError("Missing baseline blob: " + p)
        size = int(header[2]); pos = end + 1
        data[p] = raw[pos:pos + size]; pos += size + 1
    if pos != len(raw):
        raise ValueError("Unexpected Git batch remainder")
    return data


def freeze_manifest():
    obj = {"commit": BASE, "files": {p: sha(b) for p, b in baseline_lean().items()}}
    text = json.dumps(obj, indent=2) + "\n"
    path = HERE / "FROZEN_SHA256.json"
    if path.exists() and path.read_text(encoding="utf-8") != text:
        raise ValueError("FROZEN_SHA256.json differs from exact Git baseline")
    path.write_text(text, encoding="utf-8", newline="\n")


def integrity():
    freeze_manifest()
    baseline = json.loads((HERE / "FROZEN_SHA256.json").read_text(encoding="utf-8"))
    expected = {p: sha(b) for p, b in baseline_lean().items()}
    if baseline != {"commit": BASE, "files": expected}:
        raise ValueError("Frozen manifest mismatch")
    bad = [p for p, digest in expected.items()
           if not (ROOT / p).is_file() or sha((ROOT / p).read_bytes()) != digest]
    new_lean = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / "P21").rglob("*.lean")
                      if p.relative_to(ROOT).as_posix() not in expected)
    write("FROZEN_SOURCE_INTEGRITY.txt",
          f"Base: {BASE}\nProtected mathematical Lean source: {len(expected)}\n"
          f"FROZEN SOURCE INTEGRITY: {len(expected)-len(bad)}/{len(expected)}\n"
          + ("SOURCE_CHANGED: NO\n" if not bad else "SOURCE_CHANGED: YES\n" + "\n".join(bad) + "\n")
          + "New M3B2 mathematical modules:\n" + "\n".join(new_lean) + "\n")
    if bad:
        raise ValueError("Frozen source changed: " + repr(bad))
    record("frozen_source_integrity", f"{len(expected)}/{len(expected)}")
    record("source_changed", False)
    return expected


def module_name(path):
    return path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def new_modules():
    old = baseline_lean()
    return [p for p in sorted((ROOT / "P21").rglob("*.lean"))
            if p.relative_to(ROOT).as_posix() not in old]


def inventory_public(source, filename):
    """Inventory explicit public declarations; private helpers remain transitively audited."""
    rows, scopes = [], []
    for number, line in enumerate(V.SCANNER.code_only(source).splitlines(), 1):
        line = line.strip()
        opening = re.fullmatch(r"(namespace|section)(?:\s+(\S+))?", line)
        if opening:
            scopes.append((opening[1], opening[2] or "")); continue
        if re.fullmatch(r"end(?:\s+\S+)?", line):
            if not scopes: raise ValueError(f"Unbalanced scope: {filename}:{number}")
            scopes.pop(); continue
        if re.match(r"private\s+(theorem|lemma|def|abbrev|structure|inductive)", line):
            continue
        match = re.match(r"(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.'\u0080-\uffff]+)", line)
        if match:
            name = ".".join([n for k, n in scopes if k == "namespace"] + [match[2]])
            rows.append(dict(name=name, kind=match[1], file=filename, line=number))
    if scopes: raise ValueError("Unclosed scope: " + filename)
    return rows


def declarations():
    paths = new_modules()
    if not paths:
        raise ValueError("No M3B2 modules")
    rows = [r for p in paths for r in inventory_public(
        p.read_text(encoding="utf-8-sig"), p.relative_to(ROOT).as_posix())]
    names = [r["name"] for r in rows]
    if len(names) != len(set(names)):
        raise ValueError("Duplicate explicit declaration")
    required = json.loads((HERE / "MILESTONE.json").read_text(encoding="utf-8"))["required_theorems"]
    missing = set(required) - set(names)
    if missing:
        raise ValueError("Missing required theorem declarations: " + repr(missing))
    imports = "".join("import " + module_name(p) + "\n" for p in paths)
    (HERE / "GeneratedAxiomCheck.lean").write_text(
        imports + "\nset_option linter.auxLemma false\n" +
        "\n".join("#print axioms " + n for n in names) + "\n", encoding="utf-8", newline="\n")
    (HERE / "GeneratedStatementCheck.lean").write_text(
        imports + "\n" + "\n".join("#check " + n for n in names) +
        "\n#print P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement\n", encoding="utf-8", newline="\n")
    (HERE / "DECLARATIONS.json").write_text(json.dumps(rows, indent=2, ensure_ascii=False) + "\n",
                                               encoding="utf-8", newline="\n")
    write("M3B2_MODULE_LIST.txt", "\n".join(map(module_name, paths)) + "\n")
    record("m3b2_module_count", len(paths)); record("m3b2_declaration_count", len(rows))
    return paths, rows


def debt():
    V.debt()
    src = EVIDENCE / "PROOF_DEBT_REPORT.txt"
    write("PROOF_DEBT_REPORT_M3B2.txt", src.read_text(encoding="utf-8"))


def axioms(rows):
    names = [r["name"] for r in rows]
    run(lake() + ["env", "lean", "verification/m3b2/GeneratedAxiomCheck.lean"],
        "AXIOM_REPORT_M3B2.txt")
    found = V.parse_axioms((EVIDENCE / "AXIOM_REPORT_M3B2.txt").read_text(encoding="utf-8"), names)
    write("AXIOM_SUMMARY.json", json.dumps({"checked_declarations": len(found),
          "project_specific_axioms": 0, "declarations": found}, indent=2) + "\n")
    record("project_specific_axioms", 0); record("axiom_roots", len(found))


def dag():
    graph = {}
    for p in [ROOT / "P21.lean"] + sorted((ROOT / "P21").rglob("*.lean")):
        code = V.SCANNER.code_only(p.read_text(encoding="utf-8-sig"))
        graph[module_name(p)] = re.findall(r"^import\s+([\w.]+)", code, re.M)
    active, done = set(), set()
    def visit(n):
        if n in active: raise ValueError("Circular import: " + n)
        if n in done: return
        active.add(n)
        for child in graph.get(n, []): visit(child)
        active.remove(n); done.add(n)
    for n in graph: visit(n)
    root = "P21.Nonsymmetric.ColorCap.DPE.Exhaustion"
    ancestors = set()
    def collect(n):
        if n in ancestors: return
        ancestors.add(n)
        for child in graph.get(n, []): collect(child)
    collect(root)
    forbidden = {"P21.Nonsymmetric.ColorCap.FullColorCap",
                 "P21.Nonsymmetric.SelectedExtraction",
                 "P21.Nonsymmetric.ActualClassification",
                 "P21.Nonsymmetric.ColorCap.MinimumOneProof"}
    violations = sorted(ancestors & forbidden)
    write("DEPENDENCY_DAG_CHECK.txt", json.dumps(graph, indent=2) + "\nIMPORT DAG: ACYCLIC\n")
    write("CIRCULARITY_CHECK.txt", "DPE root: " + root + "\nTransitive imports:\n" +
          "\n".join(sorted(ancestors)) + "\nForbidden downstream imports: " + repr(violations) + "\n")
    if violations:
        raise ValueError("DPE reverse dependency: " + repr(violations))
    record("dependency_dag", "PASS"); record("dpe_circularity", "PASS")


def source_snapshot():
    suffixes = {".lean", ".py", ".ps1", ".yml", ".yaml", ".md", ".json"}
    names = git("ls-files", "--cached", "--others", "--exclude-standard", "-z").decode().split("\0")
    return {n: sha((ROOT / n).read_bytes()) for n in sorted(set(names))
            if n and Path(n).suffix in suffixes and (ROOT / n).is_file()}


def verify(fresh=False):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    record("m3b2_verification_exit_code", None)
    integrity(); paths, rows = declarations(); debt(); dag()
    generated = {"verification/m3b2/GeneratedAxiomCheck.lean",
                 "verification/m3b2/GeneratedStatementCheck.lean",
                 "verification/m3b2/DECLARATIONS.json",
                 "verification/m3b2/FROZEN_SHA256.json"}
    before = {n: h for n, h in source_snapshot().items() if n not in generated}
    if fresh and any((ROOT / ".lake/build").rglob("*.olean")):
        raise ValueError("--fresh requires an empty project .lake/build")
    record("fresh_root_build", fresh)
    run(lake() + ["build"], "ROOT_BUILD_LOG.txt")
    run(lake() + ["build"] + list(map(module_name, paths)), "M3B2_BUILD_LOG.txt")
    axioms(rows)
    run(lake() + ["env", "lean", "verification/m3b2/GeneratedStatementCheck.lean"],
        "STATEMENT_INSPECTION.txt")
    regressions = sorted(HERE.glob("*Regression.lean"))
    for i, p in enumerate(regressions):
        run(lake() + ["env", "lean", str(p.relative_to(ROOT))], "M3B2_VERIFICATION_LOG.txt",
            append=i != 0)
    run(lake() + ["env", "lean", "verification/m3b2/StatementRegression.lean"],
        "M3B2_VERIFICATION_LOG.txt", append=True)
    for directory, pattern in [("verification/m2", "test_debt_scan.py"),
                               ("verification/m2b", "test_*.py"), ("ci", "test_*.py")]:
        run([sys.executable, "-m", "unittest", "discover", "-s", directory, "-p", pattern, "-v"],
            "SCANNER_TEST_LOG.txt", append=directory != "verification/m2")
    integrity(); debt(); dag()
    after = {n: h for n, h in source_snapshot().items() if n not in generated}
    if before != after:
        raise ValueError("Executable source changed during verification")
    write("VERIFIED_SOURCE_SHA256.json", json.dumps(source_snapshot(), indent=2) + "\n")
    record("verified_source_integrity", "PASS")
    record("m3b2_verification_exit_code", 0)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--generate", action="store_true")
    args = parser.parse_args()
    if args.generate:
        integrity(); declarations(); debt(); dag()
    else:
        verify(args.fresh)
