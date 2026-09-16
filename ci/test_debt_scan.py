import unittest
from debt_scan import code_only, forbidden_tokens

class DebtScannerTest(unittest.TestCase):
    def test_nested_comments_are_not_declarations(self):
        self.assertEqual(forbidden_tokens('/- axiom x : False /- sorry -/ admit -/\ntheorem t : True := by trivial'), [])

    def test_line_comment_and_documentation(self):
        self.assertEqual(forbidden_tokens('-- unsafe\n/-! sorryAx opaque -/\ndef t := 1'), [])

    def test_strings_with_comment_markers_and_escaped_quotes(self):
        self.assertEqual(forbidden_tokens(r'def x := "sorry /- axiom -/ \"admit\""'), [])

    def test_raw_string(self):
        self.assertEqual(forbidden_tokens('def x := r##"sorry "unsafe" admit"##'), [])

    def test_actual_debt_is_not_hidden_by_nearby_comment(self):
        self.assertEqual(forbidden_tokens('/- safe -/ theorem x : False := by sorry -- admit'), ['sorry'])

    def test_every_forbidden_token(self):
        self.assertEqual(forbidden_tokens('sorry admit axiom sorryAx unsafe opaque'),
                         ['sorry', 'admit', 'axiom', 'sorryAx', 'unsafe', 'opaque'])

    def test_longer_identifiers(self):
        self.assertEqual(forbidden_tokens("def sorry_count := 0\ndef axioms := 0\ndef admit' := 0"), [])

    def test_line_numbers_preserved(self):
        self.assertEqual(code_only('/- x\ny -/\n"a\nb"').count('\n'), 3)

    def test_unterminated_comment_and_string_fail_closed(self):
        for source in ['/- sorry', '"sorry', 'r#"sorry']:
            with self.assertRaises(ValueError):
                code_only(source)

    def test_interpolated_strings_fail_closed(self):
        with self.assertRaises(ValueError):
            code_only('def x := s!"{by sorry}"')

    def test_character_literals_cannot_hide_debt(self):
        source = "def a : Char := '\"'\ntheorem bad : False := by sorry\ndef b : Char := '\"'"
        with self.assertRaises(ValueError):
            forbidden_tokens(source)

    def test_character_literals_fail_closed(self):
        for source in ["def x := 'a'", r"def x := '\n'", r"def x := '\''"]:
            with self.assertRaises(ValueError):
                code_only(source)

    def test_set_image_notation_remains_code(self):
        self.assertEqual(forbidden_tokens("f '' S\ntheorem bad : False := by sorry"), ['sorry'])

if __name__ == '__main__':
    unittest.main()
