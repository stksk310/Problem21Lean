#!/usr/bin/env python3
"""Validate the frozen Section 10 certificate and emit transparent Lean data."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SUPPLEMENT = ROOT / "reference_inputs" / "P21_supplement_v1.zip"
DEFAULT_OUTPUT_DIR = ROOT / "P21" / "Nonsymmetric" / "Chain" / "C10"

SUPPLEMENT_SHA = "24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e"
TABLE_SHA = "495504b4bcb8427db04b242cf09b83fbe7bde1188f9324b7e977036a5a4db9b3"
VERIFIER_SHA = "23fcf03275bbe36ef7b9ca78a6cddb6b75dd1f04216d3675fbe0da759b9d048e"
RESULT_SHA = "12a22a7ed7899ccb10cb8ff608ca4fc738da76ec0ed761c5fd72a4ab87967087"
STDOUT_SHA = "a298d66b61ca2b82ce9a429cbb795b7bd56c83f85795da7781e5c043ae12425f"

TABLE_A = "supplement/verification_scripts/EUCLIDEAN/TERMINAL_POSITIVITY_COEFFICIENTS.json"
TABLE_B = "supplement/coefficient_tables/TERMINAL_POSITIVITY_COEFFICIENTS.json"
VERIFIER = "supplement/verification_scripts/EUCLIDEAN/verify_euclidean_closure.py"
RESULT = "supplement/verification_scripts/EUCLIDEAN/verification_result.json"
EXPECTED_RESULT = "supplement/expected_outputs/EUCLIDEAN_verification_result.json"
EXPECTED_STDOUT = "supplement/expected_outputs/EUCLIDEAN_stdout.txt"

VARIABLES = [
    "p0", "q0", "s0", "t0", "r0", "delta0", "beta0", "aj0",
    "g0", "alpha0", "bk0", "nu0", "h0", "z0", "x0", "w0",
]
TERM_COUNT = 3234
IDENTITY_COUNT = 35
TOTAL_DEGREE = 7
CONSTANT = 63
CHUNK_SIZE = 90


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fail(message: str) -> "NoReturn":
    raise SystemExit(message)


def load_and_validate(supplement: Path) -> dict:
    raw_zip = supplement.read_bytes()
    if sha256(raw_zip) != SUPPLEMENT_SHA:
        fail("supplement ZIP SHA-256 mismatch")

    with zipfile.ZipFile(supplement) as archive:
        table_a = archive.read(TABLE_A)
        table_b = archive.read(TABLE_B)
        verifier = archive.read(VERIFIER)
        result = archive.read(RESULT)
        expected_result = archive.read(EXPECTED_RESULT)
        expected_stdout = archive.read(EXPECTED_STDOUT)

    if table_a != table_b:
        fail("EUCLIDEAN coefficient tables are not byte-identical")
    if sha256(table_a) != TABLE_SHA or sha256(table_b) != TABLE_SHA:
        fail("EUCLIDEAN coefficient table SHA-256 mismatch")
    if sha256(verifier) != VERIFIER_SHA:
        fail("frozen verifier SHA-256 mismatch")
    if result != expected_result or sha256(result) != RESULT_SHA:
        fail("frozen verifier result mismatch")
    if sha256(expected_stdout) != STDOUT_SHA:
        fail("frozen verifier stdout SHA-256 mismatch")

    result_data = json.loads(result)
    stdout_data = json.loads(expected_stdout)
    if result_data.get("status") != "PASS" or result_data.get("identity_count") != IDENTITY_COUNT:
        fail("frozen verifier result summary mismatch")
    if stdout_data != {
        "status": "PASS",
        "identities": IDENTITY_COUNT,
        "positive_monomials": TERM_COUNT,
        "constant": CONSTANT,
    }:
        fail("frozen verifier stdout summary mismatch")

    data = json.loads(table_a)
    terms = data.get("terms")
    if data.get("variables") != VARIABLES or not isinstance(terms, list) or len(terms) != TERM_COUNT:
        fail("certificate shape mismatch")
    constants = []
    for term in terms:
        coefficient = term.get("coefficient")
        exponents = term.get("exponents")
        if not isinstance(coefficient, int) or coefficient < 0:
            fail("malformed or negative certificate coefficient")
        if not isinstance(exponents, list) or len(exponents) != len(VARIABLES):
            fail("malformed certificate exponent vector")
        if any(not isinstance(exponent, int) or exponent < 0 for exponent in exponents):
            fail("malformed or negative certificate exponent")
        if not any(exponents):
            constants.append(term)
    if len(constants) != 1 or constants[0]["coefficient"] != CONSTANT:
        fail("certificate constant mismatch")
    if max(sum(term["exponents"]) for term in terms) != TOTAL_DEGREE:
        fail("certificate total degree mismatch")
    return data


def render(data: dict, output_dir: Path) -> dict[Path, bytes]:
    all_terms = data["terms"]
    constant = next(term for term in all_terms if not any(term["exponents"]))
    terms = [term for term in all_terms if any(term["exponents"])]
    exponent_fields = [f"e_{variable}" for variable in VARIABLES]
    namespace = "P21.Nonsymmetric.Chain.C10.TerminalCertificateData"
    nonnegative_product = "Int.ofNat_nonneg term.coefficient"
    for variable, field in zip(VARIABLES, exponent_fields, strict=True):
        nonnegative_product = (
            f"mul_nonneg ({nonnegative_product}) "
            f"(pow_nonneg h_{variable} term.{field})"
        )

    types = [
        "/- Generated from the frozen 3234-monomial Section 10 table. -/",
        "import Mathlib",
        "",
        f"namespace {namespace}",
        "",
        f'def tableSha256 : String := "{TABLE_SHA}"',
        f"def termCount : Nat := {len(all_terms)}",
        f"def totalDegree : Nat := {TOTAL_DEGREE}",
        f"def constantTerm : Nat := {constant['coefficient']}",
        "",
        "structure Variables where",
        *[f"  {variable} : ℤ" for variable in VARIABLES],
        "",
        "structure Term where",
        "  coefficient : Nat",
        *[f"  {field} : Nat" for field in exponent_fields],
        "",
        "def evalTerm (y : Variables) (term : Term) : ℤ :=",
        "  term.coefficient * "
        + " * ".join(
            f"y.{variable} ^ term.{field}"
            for variable, field in zip(VARIABLES, exponent_fields, strict=True)
        ),
        "",
        "theorem evalTerm_nonneg (y : Variables)",
        *[f"    (h_{variable} : 0 ≤ y.{variable})" for variable in VARIABLES],
        "    (term : Term) : 0 ≤ evalTerm y term := by",
        "  exact " + nonnegative_product,
        "",
        f"end {namespace}",
        "",
    ]
    outputs = {
        output_dir / "GeneratedTerminalCertificateTypes.lean": "\n".join(types).encode()
    }

    chunks = [terms[index:index + CHUNK_SIZE] for index in range(0, len(terms), CHUNK_SIZE)]
    for chunk_index, chunk in enumerate(chunks):
        lines = [
            "/- Generated frozen Section 10 certificate data. -/",
            "import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateTypes",
            "",
            f"namespace {namespace}",
            "",
            f"def terms{chunk_index} : List Term := [",
        ]
        for index, term in enumerate(chunk):
            fields = [f"coefficient := {term['coefficient']}"]
            fields.extend(
                f"{field} := {exponent}"
                for field, exponent in zip(exponent_fields, term["exponents"], strict=True)
            )
            comma = "," if index + 1 < len(chunk) else ""
            lines.append("  { " + ", ".join(fields) + " }" + comma)
        lines.extend(["]", "", f"end {namespace}", ""])
        outputs[output_dir / f"GeneratedTerminalCertificateData{chunk_index:02d}.lean"] = (
            "\n".join(lines).encode()
        )

    imports = [
        f"import P21.Nonsymmetric.Chain.C10.GeneratedTerminalCertificateData{index:02d}"
        for index in range(len(chunks))
    ]
    concatenation = " ++ ".join(f"terms{index}" for index in range(len(chunks)))
    hypotheses = " ".join(f"h_{variable}" for variable in VARIABLES)
    aggregate = [
        "/- Generated frozen Section 10 certificate aggregation and positivity theorem. -/",
        *imports,
        "",
        f"namespace {namespace}",
        "",
        f"def terms : List Term := {concatenation}",
        f"def polynomial (y : Variables) : ℤ := {CONSTANT} + (terms.map (evalTerm y)).sum",
        "",
        "theorem polynomial_pos (y : Variables)",
        *[f"    (h_{variable} : 0 ≤ y.{variable})" for variable in VARIABLES],
        "    : 0 < polynomial y := by",
        "  have hsum : 0 ≤ (terms.map (evalTerm y)).sum := by",
        "    apply List.sum_nonneg",
        "    intro value hvalue",
        "    simp only [List.mem_map] at hvalue",
        "    rcases hvalue with ⟨term, _, rfl⟩",
        f"    exact evalTerm_nonneg y {hypotheses} term",
        "  simp only [polynomial]",
        "  omega",
        "",
        f"end {namespace}",
        "",
    ]
    outputs[output_dir / "GeneratedTerminalCertificate.lean"] = "\n".join(aggregate).encode()
    return outputs


def write_outputs(outputs: dict[Path, bytes], output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    expected = set(outputs)
    for stale in output_dir.glob("GeneratedTerminalCertificate*.lean"):
        if stale not in expected:
            stale.unlink()
    for path, content in outputs.items():
        temporary = path.with_suffix(path.suffix + ".tmp")
        temporary.write_bytes(content)
        temporary.replace(path)


def check_outputs(outputs: dict[Path, bytes]) -> None:
    for path, content in outputs.items():
        if not path.exists() or path.read_bytes() != content:
            fail(f"generated file is stale: {path}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--supplement", type=Path, default=DEFAULT_SUPPLEMENT)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    data = load_and_validate(args.supplement)
    outputs = render(data, args.output_dir)
    if args.check:
        check_outputs(outputs)
    else:
        write_outputs(outputs, args.output_dir)
    aggregate = b"".join(outputs[path] for path in sorted(outputs))
    summary = {
        "status": "PASS",
        "identities": IDENTITY_COUNT,
        "terms": TERM_COUNT,
        "degree": TOTAL_DEGREE,
        "constant": CONSTANT,
        "variables": VARIABLES,
        "table_sha256": TABLE_SHA,
        "output_sha256": sha256(aggregate),
        "files": len(outputs),
    }
    print(json.dumps(summary, separators=(",", ":")))


if __name__ == "__main__":
    main()
