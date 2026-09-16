"""Adversarial checks for CI integrity and axiom gates (no proof changes)."""
import tempfile
from pathlib import Path
import unittest

import m2a_audit as audit


class IntegrityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.data = {'P21.lean': b'import P21.Basic\r\n',
                     'P21/Symmetric/Closure.lean': b'theorem demo : True := trivial\n',
                     'verification/m2/DECLARATIONS.json': b'[]\n',
                     'README.md': b'candidate\n'}
        for p, b in self.data.items():
            f = self.root / p
            f.parent.mkdir(parents=True, exist_ok=True)
            f.write_bytes(b)

    def check(self, extra=()):
        return audit.compare_sources(self.data, self.root, list(self.data) + list(extra))

    def test_unchanged_candidate(self):
        self.assertEqual(self.check(), [])

    def test_one_changed_lean_byte_fails(self):
        (self.root / 'P21.lean').write_bytes(b'import P21.Basic\n')
        self.assertTrue(self.check())

    def test_added_lean_fails(self):
        self.assertTrue(self.check(['ci/Hidden.lean']))

    def test_missing_metadata_fails(self):
        (self.root / 'verification/m2/DECLARATIONS.json').unlink()
        self.assertTrue(self.check())

    def test_readme_append_only(self):
        (self.root / 'README.md').write_bytes(b'candidate\nCI appendix\n')
        self.assertEqual(self.check(), [])
        (self.root / 'README.md').write_bytes(b'new claim\n')
        self.assertTrue(self.check())

    def test_nested_and_other_new_modules_enumerated(self):
        data = {'P21.lean': b'', 'P21/Basic.lean': b'',
                'P21/Symmetric/Nested/New.lean': b'', 'P21/Other.lean': b'',
                'verification/Check.lean': b''}
        self.assertEqual(audit.module_names(data, {'P21.lean', 'P21/Basic.lean'}),
                         ['P21.Other', 'P21.Symmetric.Nested.New'])


class AxiomTests(unittest.TestCase):
    def test_allowed_and_empty(self):
        output = "'A' depends on axioms: [propext, Classical.choice, Quot.sound]\n'B' does not depend on any axioms\n"
        self.assertEqual(len(audit.parse_axioms(output, {'A', 'B'})), 2)

    def test_project_axiom_fails(self):
        with self.assertRaises(ValueError):
            audit.parse_axioms("'A' depends on axioms: [STD_SYM_GLUE]", {'A'})

    def test_missing_root_fails(self):
        with self.assertRaises(ValueError):
            audit.parse_axioms("'A' does not depend on any axioms", {'A', 'B'})

    def test_warning_fails(self):
        with self.assertRaises(ValueError):
            audit.parse_axioms("warning: proof debt\n'A' does not depend on any axioms", {'A'})


if __name__ == '__main__':
    unittest.main()
