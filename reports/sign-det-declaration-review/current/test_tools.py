"""Controls for source qualification and complete extra-constant accounting."""
import tempfile
import unittest
from pathlib import Path

from normalize import compiler_kind, source_names


class NamingTest(unittest.TestCase):
    def test_nested_namespace_and_global_override(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Example.lean'
            source.write_text('namespace Hex.SignDet\nsection\nnamespace Dag\n'
                              'theorem selectedSigns_values : True := by trivial\n'
                              'theorem _root_.Vector.transport : True := by trivial\n'
                              'end Dag\nend\nend Hex.SignDet\n')
            self.assertEqual(source_names(source), {
                'selectedSigns_values': 'Hex.SignDet.Dag.selectedSigns_values',
                '_root_.Vector.transport': 'Vector.transport'})

    def test_comment_declaration_is_not_source_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Example.lean'
            source.write_text('/- namespace False\ntheorem omitted : False := by sorry\n-/\n'
                              'namespace Real\ndef actual : Nat := 1\nend Real\n')
            self.assertEqual(source_names(source), {'actual': 'Real.actual'})


class ExtraTest(unittest.TestCase):
    def test_unknown_extra_is_refused(self):
        with self.assertRaisesRegex(ValueError, 'unaccounted'):
            compiler_kind({'kind': 'theorem', 'name': 'Hex.SignDet.missing_statement'})

    def test_recognized_categories(self):
        examples = {'equation': 'eq_1', 'matcher': 'match_1_2', 'proof': '_proof_1_2',
                    'simp': 'congr_simp', 'recursion': '_unsafe_rec', 'structure': 'recOn'}
        for kind, suffix in examples.items():
            self.assertEqual(compiler_kind({'kind': 'definition', 'name': 'A.' + suffix}), kind)

    def test_constant_kind_accounts_constructor_and_recursor(self):
        for kind in ('constructor', 'recursor'):
            self.assertEqual(compiler_kind({'kind': kind, 'name': 'A.generated'}), kind)


if __name__ == '__main__':
    unittest.main()
