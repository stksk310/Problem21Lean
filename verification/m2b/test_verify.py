"""Regression tests for M2B audit coverage and fail-closed behavior."""
import importlib.util
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('m2b_test_verify', HERE / 'verify.py')
V = importlib.util.module_from_spec(spec)
spec.loader.exec_module(V)
spec2 = importlib.util.spec_from_file_location('m2b_test_ci', HERE.parents[1] / 'ci/m2b_audit.py')
C = importlib.util.module_from_spec(spec2)
spec2.loader.exec_module(C)


class InventoryTests(unittest.TestCase):
    def test_nested_namespace_and_section(self):
        rows = V.inventory_source('namespace A\nsection\ntheorem one : True := by trivial\nend\nnamespace B\ndef two := 2\nend B\nend A\n', 'X.lean')
        self.assertEqual([r['name'] for r in rows], ['A.one', 'A.B.two'])

    def test_comment_not_a_declaration(self):
        self.assertEqual(V.inventory_source('/- theorem phantom : False := by x -/\n', 'X'), [])

    def test_primed_name(self):
        self.assertEqual(V.inventory_source("theorem test' : True := by trivial", 'X')[0]['name'], "test'")

    def test_scope_mismatch(self):
        with self.assertRaises(ValueError):
            V.inventory_source('namespace A\ntheorem t : True := by trivial', 'X')

    def test_private_fails_closed(self):
        with self.assertRaises(ValueError):
            V.inventory_source('private theorem hidden : True := by trivial', 'X')

    def test_axiom_coverage(self):
        text = "'A.t' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
        self.assertEqual(set(V.parse_axioms(text, {'A.t'})), {'A.t'})
        with self.assertRaises(ValueError):
            V.parse_axioms(text, {'A.t', 'A.missing'})

    def test_axiom_debt_and_duplicate(self):
        for text in ["'A.t' depends on axioms: [Project.assumption]",
                     "'A.t' does not depend on any axioms\n" * 2]:
            with self.assertRaises(ValueError):
                V.parse_axioms(text, {'A.t'})

    def test_additional_shortcuts_banned(self):
        self.assertTrue({'native_decide', 'run_tac', 'opaque', 'sorry', 'axiom'} <= V.BANNED)

    def test_frozen_file_count(self):
        self.assertEqual(len(V.protected()), 57)


class ArchiveTests(unittest.TestCase):
    def archive(self, entries):
        import tempfile
        import zipfile
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        path = Path(tmp.name) / 'candidate.zip'
        with zipfile.ZipFile(path, 'w') as z:
            for name, content in entries:
                z.writestr(name, content)
        return path

    def test_traversal_rejected(self):
        p = self.archive([('candidate/../escape', b'bad')])
        with self.assertRaises(ValueError):
            C.archive_data(p, V.sha(p.read_bytes()))

    def test_hash_rejected(self):
        p = self.archive([('candidate/x', b'x')])
        with self.assertRaises(ValueError):
            C.archive_data(p, '0' * 64)

    def test_manifest_coverage_rejected(self):
        p = self.archive([('candidate/x', b'x'), ('candidate/MANIFEST_SHA256.json', b'{"files":{}}')])
        with self.assertRaises(ValueError):
            C.archive_data(p, V.sha(p.read_bytes()))


if __name__ == '__main__':
    unittest.main()
