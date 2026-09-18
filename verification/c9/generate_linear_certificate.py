#!/usr/bin/env python3
"""Generate split Lean proof data from the frozen Section 9 certificate."""
from __future__ import annotations
import argparse, hashlib, json, zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SUPPLEMENT = ROOT / "reference_inputs" / "P21_supplement_v1.zip"
OUTPUT_DIR = ROOT / "P21" / "Nonsymmetric" / "Chain" / "C9"
OUTPUT = OUTPUT_DIR / "GeneratedLinearCertificate.lean"
SUPPLEMENT_SHA = "24a02d34651c35aa3d07f707fd38b7ca29d0f8bbfa86190d956657308b498c5e"
TABLE_SHA = "9ba4fdcbdc1b5440785232e97e8cf8d729c3cf1254d87551d3a90d9abbff5916"
VERIFIER_SHA = "bcdedc3525a397601fd49704629e221f0e34e6d5ffcdc0c9c8e22d3f25775ae1"
TABLE_A = "supplement/verification_scripts/LINEAR/I_FIT_POSITIVE_COEFFICIENTS.json"
TABLE_B = "supplement/coefficient_tables/I_FIT_POSITIVE_COEFFICIENTS.json"
VERIFIER = "supplement/verification_scripts/LINEAR/verify_D_linear.py"
VARIABLES = ["f", "r", "delta", "beta", "g", "u", "alpha", "w", "theta", "eps", "k", "a_j", "b_k"]

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def render(data: dict) -> dict[Path, bytes]:
    all_terms = data["terms"]
    constant = next(t for t in all_terms if not any(t["exponents"]))
    terms = [t for t in all_terms if any(t["exponents"])]
    efields = [f"e_{v}" for v in VARIABLES]
    types = [
        "/- Generated from the frozen 715-term table. -/", "import Mathlib", "",
        "namespace P21.Nonsymmetric.ChainCore.C9.LinearCertificateData", "",
        f"def tableSha256 : String := \"{TABLE_SHA}\"", f"def termCount : Nat := {len(all_terms)}",
        f"def constantTerm : Nat := {constant['coefficient']}", "",
        "structure Variables where", *[f"  {v} : ℤ" for v in VARIABLES], "",
        "structure Term where", "  coefficient : Nat", *[f"  {e} : Nat" for e in efields], "",
        "def evalTerm (y : Variables) (t : Term) : ℤ :=",
        "  t.coefficient * " + " * ".join(f"y.{v} ^ t.{e}" for v, e in zip(VARIABLES, efields, strict=True)), "",
        "theorem evalTerm_nonneg (y : Variables)", *[f"    (h_{v} : 0 ≤ y.{v})" for v in VARIABLES],
        "    (t : Term) : 0 ≤ evalTerm y t := by", "  simp only [evalTerm]", "  positivity", "",
        "end P21.Nonsymmetric.ChainCore.C9.LinearCertificateData", "",
    ]
    outputs = {OUTPUT_DIR / "GeneratedLinearCertificateTypes.lean": "\n".join(types).encode()}
    chunks = [terms[i:i + 90] for i in range(0, len(terms), 90)]
    for ci, chunk in enumerate(chunks):
        lines = ["/- Generated frozen certificate data. -/",
                 "import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateTypes", "",
                 "namespace P21.Nonsymmetric.ChainCore.C9.LinearCertificateData", "",
                 f"def terms{ci} : List Term := ["]
        for i, term in enumerate(chunk):
            fields = [f"coefficient := {term['coefficient']}"]
            fields += [f"{e} := {x}" for e, x in zip(efields, term["exponents"], strict=True)]
            lines.append("  { " + ", ".join(fields) + " }" + ("," if i + 1 < len(chunk) else ""))
        lines += ["]", "", "end P21.Nonsymmetric.ChainCore.C9.LinearCertificateData", ""]
        outputs[OUTPUT_DIR / f"GeneratedLinearCertificateData{ci}.lean"] = "\n".join(lines).encode()
    imports = [f"import P21.Nonsymmetric.Chain.C9.GeneratedLinearCertificateData{i}" for i in range(len(chunks))]
    concat = " ++ ".join(f"terms{i}" for i in range(len(chunks)))
    final = ["/- Generated frozen certificate aggregation and positivity theorem. -/", *imports, "",
             "namespace P21.Nonsymmetric.ChainCore.C9.LinearCertificateData", "",
             f"def terms : List Term := {concat}",
             f"def polynomial (y : Variables) : ℤ := {constant['coefficient']} + (terms.map (evalTerm y)).sum", "",
             "theorem polynomial_pos (y : Variables)", *[f"    (h_{v} : 0 ≤ y.{v})" for v in VARIABLES],
             "    : 0 < polynomial y := by", "  have hs : 0 ≤ (terms.map (evalTerm y)).sum := by",
             "    apply List.sum_nonneg", "    intro z hz", "    simp only [List.mem_map] at hz",
             "    rcases hz with ⟨t, _, rfl⟩",
             "    exact evalTerm_nonneg y " + " ".join(f"h_{v}" for v in VARIABLES) + " t",
             "  simp only [polynomial]", "  omega", "",
             "end P21.Nonsymmetric.ChainCore.C9.LinearCertificateData", ""]
    outputs[OUTPUT] = "\n".join(final).encode()
    return outputs

def main() -> None:
    parser = argparse.ArgumentParser(); parser.add_argument("--check", action="store_true"); args = parser.parse_args()
    raw_zip = SUPPLEMENT.read_bytes()
    if sha(raw_zip) != SUPPLEMENT_SHA: raise SystemExit("supplement ZIP SHA-256 mismatch")
    with zipfile.ZipFile(SUPPLEMENT) as archive:
        table_a, table_b, verifier = archive.read(TABLE_A), archive.read(TABLE_B), archive.read(VERIFIER)
    if table_a != table_b or sha(table_a) != TABLE_SHA or sha(verifier) != VERIFIER_SHA:
        raise SystemExit("frozen certificate input mismatch")
    data = json.loads(table_a); terms = data.get("terms", []); constants = [t for t in terms if not any(t["exponents"])]
    if data.get("variables") != VARIABLES or len(terms) != 715: raise SystemExit("certificate shape mismatch")
    if len(constants) != 1 or constants[0]["coefficient"] != 35: raise SystemExit("certificate constant mismatch")
    if any(t["coefficient"] < 0 or len(t["exponents"]) != 13 for t in terms):
        raise SystemExit("malformed or negative certificate term")
    rendered = render(data)
    if args.check:
        for path, content in rendered.items():
            if not path.exists() or path.read_bytes() != content: raise SystemExit(f"generated file is stale: {path}")
    else:
        OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
        for stale in OUTPUT_DIR.glob("GeneratedLinearCertificateData*.lean"): stale.unlink()
        for path, content in rendered.items(): path.write_bytes(content)
    aggregate = b"".join(rendered[p] for p in sorted(rendered))
    print(json.dumps({"status":"PASS","terms":715,"constant":35,"table_sha256":TABLE_SHA,
                      "output_sha256":sha(aggregate),"files":len(rendered)}))

if __name__ == "__main__": main()
