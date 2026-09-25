"""Small lexer regressions for the optional proof-admission audit."""

import unittest

from check_named_admissions import ADMISSION, IMPORT, code_only


class AdmissionScannerTests(unittest.TestCase):
    def test_imports_behind_comments_and_on_one_line(self):
        source = 'public import Foo.Bar /- note -/ import Baz.Qux\n'
        self.assertEqual([m.group(1) for m in IMPORT.finditer(code_only(source))],
                         ["Foo.Bar", "Baz.Qux"])

    def test_quoted_character_does_not_hide_admission(self):
        self.assertIsNotNone(ADMISSION.search(code_only('def c := \'"\'\ntheorem bad : False := by sorry\n')))
        self.assertIsNone(ADMISSION.search(code_only('def c := \'"\'\ndef s := "sorry"\n')))

    def test_raw_string_does_not_hide_next_line(self):
        self.assertIsNotNone(ADMISSION.search(code_only('def s := r"\\"\ntheorem bad : False := by sorry\n')))
        self.assertIsNotNone(ADMISSION.search(code_only('def s := r#"\\"#\ntheorem bad : False := by sorry\n')))

    def test_other_admissions(self):
        for token in ("mkSorry", "mkSyntheticSorry", "exceptionToSorry",
                      "admitGoal", "sorryAx", "axiom bad : False",
                      "@[simp] axiom bad : False", "private axiom bad : False",
                      "constant bad : False", "theorem h : True := by stop",
                      "stop simp"):
            with self.subTest(token=token):
                self.assertIsNotNone(ADMISSION.search(code_only(token)))
        self.assertIsNone(ADMISSION.search(code_only("rw [Array.foldl_push_eq_append (stop := n) rfl]")))

    def test_interpolated_admission_fails_closed(self):
        for prefix in ("s!", "m!", "f!"):
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                code_only(f'def x := {prefix}"{{(by sorry : Nat)}}"')
        with self.assertRaises(ValueError):
            code_only('def x := m!"{\"quoted\" ++ (by sorry : String)}"')

    def test_prime_before_character_literal(self):
        source = 'def x := f x\' \'"\'\ntheorem bad : False := by sorry\n'
        self.assertIsNotNone(ADMISSION.search(code_only(source)))


if __name__ == "__main__":
    unittest.main()
