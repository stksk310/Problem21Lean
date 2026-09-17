"""Fail-closed inventory and axiom parser checks; no Lean builds or source changes."""
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch
import json

spec=importlib.util.spec_from_file_location("m3b1_under_test",Path(__file__).with_name("verify.py"))
V=importlib.util.module_from_spec(spec);spec.loader.exec_module(V)

class VerifierTests(unittest.TestCase):
    def test_frozen_path_coverage(self):
        for p in ["P21/Basic.lean","verification/m3/local-evidence/KERNEL_DECLARATION_PREFIX.txt",
                  "verification/m2/debt_scan.py","ci/m3_audit.py","lean-toolchain","lake-manifest.json",
                  "ci/candidate/P21_LEAN_M3A_NONSYMMETRIC_LOCAL_GEOMETRY_CANDIDATE_20260917.zip",
                  "ci/M3_CANDIDATE_SHA256.txt","ci/M2B_CANDIDATE_SHA256.txt"]:
            self.assertTrue(V.protect_path(p),p)
        self.assertFalse(V.protect_path(".github/workflows/m3-audit.yml"))

    def test_prefix_inventory_includes_generated_helpers(self):
        text="P21.Nonsymmetric.X.a\nP21.Nonsymmetric.X.a._proof_1\nP21.Nonsymmetric.X.a\n"
        self.assertEqual(V.prefix_names(text),{"P21.Nonsymmetric.X.a","P21.Nonsymmetric.X.a._proof_1"})

    def test_axiom_parser_rejects_project_axiom(self):
        with self.assertRaises(ValueError):
            V.V.parse_axioms("'P21.x' depends on axioms: [propext, P21.WhiteAssumption]",["P21.x"])

    def test_axiom_parser_requires_every_root(self):
        with self.assertRaises(ValueError):
            V.V.parse_axioms("'P21.x' does not depend on any axioms",["P21.x","P21.y"])

    def test_full_status_requires_exact_proof_name(self):
        data=dict(candidate="P21_LEAN_M3B1_TEST.zip",status="test",minimum_one_proved=True,
                  std_white="OPEN",required_theorems=["P21.Nonsymmetric.X"],
                  statement_regression="verification/m3b1/StatementRegression.lean")
        with patch.object(Path,"read_text",return_value=json.dumps(data)):
            with self.assertRaises(ValueError):V.milestone()

    def test_full_proof_must_be_required_root(self):
        data=dict(candidate="P21_LEAN_M3B1_TEST.zip",status="test",minimum_one_proved=True,
                  std_white="PROVED",required_theorems=["P21.Nonsymmetric.Other"],
                  minimum_one_theorem="P21.Nonsymmetric.minimum_one_proved",
                  statement_regression="verification/m3b1/StatementRegression.lean")
        with patch.object(Path,"read_text",return_value=json.dumps(data)):
            with self.assertRaises(ValueError):V.milestone()

    def test_success_boolean_is_not_string(self):
        data=dict(candidate="P21_LEAN_M3B1_TEST.zip",status="test",minimum_one_proved="false",
                  std_white="OPEN",required_theorems=["P21.Nonsymmetric.X"],
                  statement_regression="verification/m3b1/StatementRegression.lean")
        with patch.object(Path,"read_text",return_value=json.dumps(data)):
            with self.assertRaises(ValueError):V.milestone()

if __name__=="__main__":unittest.main()
