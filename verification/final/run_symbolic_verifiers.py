#!/usr/bin/env python3
"""Run the two frozen supplement verifiers under exactly SymPy 1.14.0."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[2]
SUPPLEMENT = ROOT / "reference_inputs/P21_supplement_v1.zip"
SUPPLEMENT_SHA = "24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e"

CASES = (
    {
        "name": "LINEAR",
        "verifier": "supplement/verification_scripts/LINEAR/verify_D_linear.py",
        "result": "supplement/verification_scripts/LINEAR/verification_result.json",
        "table_a": "supplement/verification_scripts/LINEAR/I_FIT_POSITIVE_COEFFICIENTS.json",
        "table_b": "supplement/coefficient_tables/I_FIT_POSITIVE_COEFFICIENTS.json",
        "table_sha": "9ba4fdcbdc1b5440785232e97e8cf8d729c3cf1254d87551d3a90d9abbff5916",
        "identities": 28,
        "monomials": 715,
        "constant": 35,
    },
    {
        "name": "EUCLIDEAN",
        "verifier": "supplement/verification_scripts/EUCLIDEAN/verify_euclidean_closure.py",
        "result": "supplement/verification_scripts/EUCLIDEAN/verification_result.json",
        "table_a": "supplement/verification_scripts/EUCLIDEAN/TERMINAL_POSITIVITY_COEFFICIENTS.json",
        "table_b": "supplement/coefficient_tables/TERMINAL_POSITIVITY_COEFFICIENTS.json",
        "table_sha": "495504b4bcb8427db04b242cf09b83fbe7bde1188f9324b7e977036a5a4db9b3",
        "identities": 35,
        "monomials": 3234,
        "constant": 63,
    },
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    import sympy

    if sympy.__version__ != "1.14.0":
        raise SystemExit(f"SymPy version mismatch: {sympy.__version__}")
    raw = SUPPLEMENT.read_bytes()
    if sha(raw) != SUPPLEMENT_SHA:
        raise SystemExit("supplement SHA mismatch")
    summaries = []
    with tempfile.TemporaryDirectory() as temp:
        with zipfile.ZipFile(SUPPLEMENT) as archive:
            archive.extractall(temp)
        root = Path(temp)
        for case in CASES:
            with zipfile.ZipFile(SUPPLEMENT) as archive:
                table_a = archive.read(case["table_a"])
                table_b = archive.read(case["table_b"])
            if table_a != table_b or sha(table_a) != case["table_sha"]:
                raise SystemExit(f"{case['name']} table mismatch")
            verifier = root / case["verifier"]
            run = subprocess.run(
                [sys.executable, str(verifier)], cwd=verifier.parent,
                text=True, encoding="utf-8", stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            if run.returncode:
                raise SystemExit(f"{case['name']} verifier failed:\n{run.stdout}")
            result = json.loads((root / case["result"]).read_text(encoding="utf-8"))
            polynomial = result.get("positive_polynomial", result.get("terminal_positive_polynomial", {}))
            count = polynomial.get("monomial_count", polynomial.get("positive_monomials"))
            constant = polynomial.get("constant_term", polynomial.get("constant"))
            if result.get("status") != "PASS" or result.get("identity_count") != case["identities"]:
                raise SystemExit(f"{case['name']} identity summary mismatch")
            if count != case["monomials"] or constant != case["constant"]:
                raise SystemExit(f"{case['name']} polynomial summary mismatch: {polynomial}")
            summaries.append({
                "name": case["name"], "status": "PASS",
                "identities": case["identities"], "positive_monomials": count,
                "constant": constant, "table_sha256": case["table_sha"],
                "stdout": run.stdout.strip(),
            })
    print(json.dumps({"sympy": sympy.__version__, "verifiers": summaries}, indent=2))


if __name__ == "__main__":
    main()
