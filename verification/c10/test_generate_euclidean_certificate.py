from __future__ import annotations

import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
GENERATOR = Path(__file__).with_name("generate_euclidean_certificate.py")
SUPPLEMENT = ROOT / "reference_inputs" / "P21_supplement_v1.zip"


def tree_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(root.glob("GeneratedTerminalCertificate*.lean")):
        digest.update(path.name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
    return digest.hexdigest()


class EuclideanCertificateGeneratorTest(unittest.TestCase):
    def run_generator(
        self, supplement: Path, output_dir: Path, *extra: str
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(GENERATOR),
                "--supplement",
                str(supplement),
                "--output-dir",
                str(output_dir),
                *extra,
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )

    def test_generates_and_checks_exact_frozen_certificate(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            output_dir = Path(raw) / "generated"
            first = self.run_generator(SUPPLEMENT, output_dir)
            self.assertEqual(first.returncode, 0, first.stderr)
            summary = json.loads(first.stdout)
            self.assertEqual(summary["status"], "PASS")
            self.assertEqual(summary["identities"], 35)
            self.assertEqual(summary["terms"], 3234)
            self.assertEqual(summary["degree"], 7)
            self.assertEqual(summary["constant"], 63)
            self.assertEqual(
                summary["variables"],
                [
                    "p0", "q0", "s0", "t0", "r0", "delta0", "beta0",
                    "aj0", "g0", "alpha0", "bk0", "nu0", "h0", "z0",
                    "x0", "w0",
                ],
            )
            types = output_dir / "GeneratedTerminalCertificateTypes.lean"
            aggregate = output_dir / "GeneratedTerminalCertificate.lean"
            self.assertIn("def termCount : Nat := 3234", types.read_text(encoding="utf-8"))
            self.assertIn("def constantTerm : Nat := 63", types.read_text(encoding="utf-8"))
            self.assertIn("theorem polynomial_pos", aggregate.read_text(encoding="utf-8"))

            before = tree_digest(output_dir)
            second = self.run_generator(SUPPLEMENT, output_dir)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(tree_digest(output_dir), before)
            checked = self.run_generator(SUPPLEMENT, output_dir, "--check")
            self.assertEqual(checked.returncode, 0, checked.stderr)
            self.assertEqual(json.loads(checked.stdout), json.loads(first.stdout))

    def test_rejects_modified_supplement(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            temporary = Path(raw)
            corrupt = temporary / "corrupt.zip"
            shutil.copyfile(SUPPLEMENT, corrupt)
            payload = bytearray(corrupt.read_bytes())
            payload[len(payload) // 2] ^= 1
            corrupt.write_bytes(payload)
            result = self.run_generator(corrupt, temporary / "generated")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("supplement ZIP SHA-256 mismatch", result.stderr)


if __name__ == "__main__":
    unittest.main()
