"""Exercise source roles and genuine clients through compiler-generated aliases."""
import unittest
import subprocess
import sys
from pathlib import Path
from audit_tools import SourceIndex, client_status, reference_graph

PAIR = 'HexSturm.Basic'
OTHER = 'HexRealClosureMathlib.Algebraic'
ROLES = {PAIR: {'category': 'Sturm production'}, OTHER: {'category': 'other Hex production'}}


def row(name, users, bases=None, base=None):
    return {'name': name, 'module': PAIR, 'users': list(users), 'user_modules': users,
            'user_bases': {user: (bases or {}).get(user, {'declaration': None, 'module': None}) for user in users},
            'base_declaration': base, 'base_module': PAIR if base else None}


class ExecutionModeTest(unittest.TestCase):
    def test_optimized_python_refused(self):
        for script in ('audit_tools.py', 'normalize.py', 'check_bindings.py'):
            result = subprocess.run([sys.executable, '-O', str(Path(__file__).with_name(script))],
                                    capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, script)
            self.assertIn('requires assertions', result.stderr, script)


class GraphTest(unittest.TestCase):
    def test_real_client_through_equation_reaches_base(self):
        rows = [row('X', {'X.eq_1': PAIR}, {'X.eq_1': {'declaration': 'X', 'module': PAIR}}),
                row('X.eq_1', {'Outside.use': OTHER}, base='X')]
        users, live, _, aliases = reference_graph(rows, {'X'}, set(), ROLES)
        self.assertIn('X', live)
        self.assertEqual(users['X'], ['Outside.use'])
        self.assertEqual(aliases['X.eq_1'], 'X')

    def test_downstream_generated_artifact_is_not_itself_a_client(self):
        rows = [row('X', {'X.congr_simp': OTHER}, {'X.congr_simp': {'declaration': 'X', 'module': PAIR}})]
        users, live, _, _ = reference_graph(rows, {'X'}, set(), ROLES)
        self.assertEqual(users['X'], [])
        self.assertNotIn('X', live)

    def test_nested_generated_names_are_collapsed(self):
        for suffix in ('_simp_1_2', '_proof_1_3', 'eq_def', 'eq_unfold', 'induct', 'fun_cases', 'induct_unfolding', 'mutual_induct', 'fun_cases_unfolding'):
            user = 'X.' + suffix
            rows = [row('X', {user: OTHER}, {user: {'declaration': 'X', 'module': PAIR}})]
            users, live, _, aliases = reference_graph(rows, {'X'}, set(), ROLES)
            self.assertEqual(aliases[user], 'X')
            self.assertEqual(users['X'], [])
            self.assertNotIn('X', live)

    def test_genuine_method_under_structure_namespace_is_preserved(self):
        user = 'Struct.newTheorem'
        rows = [row('Struct', {user: OTHER}, {user: {'declaration': 'Struct', 'module': PAIR}})]
        users, live, _, aliases = reference_graph(rows, {'Struct'}, set(), ROLES)
        self.assertEqual(users['Struct'], [user])
        self.assertIn('Struct', live)
        self.assertNotIn(user, aliases)

    def test_source_written_field_is_not_a_generated_alias(self):
        rows = [row('Struct', {'Struct.head': PAIR}, {'Struct.head': {'declaration': 'Struct', 'module': PAIR}}),
                row('Struct.head', {'Outside.use': OTHER}, base='Struct')]
        _, live, _, aliases = reference_graph(rows, {'Struct'}, {'Struct.head'}, ROLES)
        self.assertIn('Struct.head', live)
        self.assertIn('Struct', live)
        self.assertNotIn('Struct.head', aliases)

    def test_production_client_cannot_be_labelled_evidence_only(self):
        data = {'filtered_users': {'X': ['Outside.use']}, 'user_modules': {'Outside.use': OTHER}}
        with self.assertRaises(AssertionError):
            client_status('X', data, ROLES)


class SourceRoleTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index = SourceIndex()

    def test_semantic_adapters_are_production(self):
        for module in ('HexRCF.RealCoefficients.IsolationAssembly', 'HexRealClosureMathlib.Canonical'):
            self.assertEqual(self.index.resolve(module)['category'], 'other Hex production')

    def test_production_checks_are_not_tests_by_name(self):
        self.assertEqual(self.index.resolve('HexSignDetMathlib.NodeChecks')['category'], 'other Hex production')
        self.assertEqual(self.index.resolve('HexSignDetMathlib.TreeChecks')['category'], 'other Hex production')

    def test_conformance_public_import_is_evidence(self):
        self.assertEqual(self.index.resolve('HexRealClosureMathlib.ContextOperationsPublic')['category'], 'tests/conformance/manual')

    def test_trivial_root_comparison_driver_is_evidence(self):
        self.assertEqual(self.index.resolve('HexRealClosure.TrivialChecks')['category'], 'tests/conformance/manual')

    def test_unknown_module_refused(self):
        with self.assertRaises(AssertionError):
            self.index.resolve('UnknownMissingModule')


if __name__ == '__main__':
    unittest.main()
