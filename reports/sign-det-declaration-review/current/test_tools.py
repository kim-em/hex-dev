"""Controls for source qualification and complete extra-constant accounting."""
import tempfile
import importlib.util
import unittest
from unittest.mock import patch
from pathlib import Path

from normalize import compiler_kind, source_names, lexical_references


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


class ReferenceTest(unittest.TestCase):
    def test_qualified_names_do_not_borrow_same_suffix(self):
        name = 'Hex.SignDet.QueryHandle.signAt_correct'
        graph = {'public_without_downstream_production_path': [name],
                 'filtered_users': {name: []}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Mention.lean').write_text(
                'Hex.SignDet.Descriptor.signAt_correct\n'
                'QueryHandle.signAt_correct\n'
                'Hex.SignDet.QueryHandle.signAt_correct\n'
                'signAt_correct\n')
            with patch('normalize.ROOT', root), patch('normalize.REFERENCE_INPUTS', ('Mention.lean',)):
                row = lexical_references(graph)['declarations'][0]
            self.assertEqual([ref['line'] for ref in row['references']], [3])
            self.assertFalse(row['has_direct_term_reference'])


    def test_quoted_axiom_name_is_recorded(self):
        name = 'Hex.SignDet.endpoint_lower'
        graph = {'public_without_downstream_production_path': [name], 'filtered_users': {name: []}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'Mention.lean').write_text("/-- info: 'Hex.SignDet.endpoint_lower' depends on axioms: [propext] -/\n")
            with patch('normalize.ROOT', root), patch('normalize.REFERENCE_INPUTS', ('Mention.lean',)):
                refs = lexical_references(graph)['declarations'][0]['references']
            self.assertEqual(len(refs), 1)
            self.assertEqual(refs[0]['matched_name'], name)
            self.assertEqual(refs[0]['kind'], 'axiom audit')



class CheckpointTest(unittest.TestCase):
    def test_local_checkpoint_is_not_shadowed_by_sturm_helpers(self):
        base = Path(__file__).resolve().parent
        spec = importlib.util.spec_from_file_location('_test_signdet_reproduce', base / 'reproduce.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertEqual(module.load_checkpoint().BASE, base)



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
