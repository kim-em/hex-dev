"""Check both raw storage policies and reject changed field values or graphs."""
import copy
import json
from pathlib import Path
import unittest
import tempfile
import subprocess
import sys
import hashlib
from scripts.oracle.real_closure_nested_normalization import verify, trace_counts, trace_data, verify_pairs, validate_trace


class ExactTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixture = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/nested-normalization.jsonl'
        cls.rows = [json.loads(line) for line in fixture.read_text().splitlines()]

    def test_matched_exact_values(self):
        checked = [verify(row) for row in self.rows]
        self.assertEqual(checked[0]['field_residue'], checked[1]['field_residue'])
        for result in checked:
            self.assertTrue(result['exact_value_checked'])
            self.assertTrue(result['selected_root_sign_checked'])
            self.assertFalse(result['query']['mathematical_replay_checked'])

    def test_changed_inputs(self):
        for source in self.rows:
            for change in ['value', 'head', 'fraction', 'sign', 'steps', 'nodes', 'children', 'replayed']:
                with self.subTest(eager=source['eager'], change=change):
                    row = copy.deepcopy(source)
                    if change == 'value':
                        row['value'][0][0][0] += row['value'][0][0][1]
                    elif change == 'head': row['heads'][0][0] = [4, 1]
                    elif change == 'fraction': row['value'][0][0] = [2, 2]
                    elif change == 'sign': row['sign'] = True
                    elif change == 'steps': row['steps'] = -1
                    elif change == 'nodes': row['query'][1] += 1
                    elif change == 'replayed': row['query_replayed'] = False
                    elif change == 'children': row['query'][2][2][0][1] = [[0, 0]]
                    with self.assertRaises(ValueError): verify(row)

    def test_aggregate_trace(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'trace'
            packet = dict(overflow=False, counts={'0:mul': 12, '1:inverse_gcd': 1})
            def write(packet):
                operations = dict.fromkeys(['poly_gcd', 'poly_xgcd', 'poly_xgcd_left', 'poly_pseudo_gcd', 'lean_nat_gcd', 'gmp_gcd', 'gmp_gcdext'], 0)
                path.write_text('NESTED BEGIN\nNESTED END\nNESTED COUNTERS ' + json.dumps(operations) + '\nNESTED CALLBACKS ' + json.dumps(packet) + '\n')
            write(packet)
            self.assertEqual(trace_counts(path), packet['counts'])
            for bad in [dict(packet, overflow=True), dict(packet, counts={'0:mul': True}),
                        dict(packet, counts={'bad': 1}), dict(packet, counts={'0:mul': -1})]:
                write(bad)
                with self.assertRaises(ValueError): trace_counts(path)

    def test_stdin_and_pairs(self):
        script = Path(__file__).with_name('real_closure_nested_normalization.py')
        text = '\n'.join(json.dumps(row) for row in self.rows) + '\n'
        result = subprocess.run([sys.executable, str(script)], input=text, text=True,
                                capture_output=True, check=True)
        self.assertEqual(len(json.loads(result.stdout)['results']), 2)
        rejected = subprocess.run([sys.executable, str(script)], input=json.dumps(self.rows[0]),
                                  text=True, capture_output=True)
        self.assertNotEqual(rejected.returncode, 0)
        checked = [verify(row) for row in self.rows]
        verify_pairs(self.rows, checked)
        for rows, results in [(self.rows[:1], checked[:1]),
                              ([self.rows[0]] * 2, [checked[0]] * 2),
                              (self.rows * 2, checked * 2),
                              (self.rows, [checked[0], dict(checked[1], field_residue=[])])]:
            with self.assertRaises(ValueError): verify_pairs(rows, results)
        different = copy.deepcopy(self.rows)
        different[1]['heads'][0][0] = [4, 1]
        with self.assertRaises(ValueError): verify_pairs(different, checked)
        verify_pairs(self.rows[:1], checked[:1], unpaired=True)

    def test_trace_binds_workload(self):
        root = Path(__file__).resolve().parents[2]
        path = root / 'reports/bench-results/real-closure-nested-diagnostics-c7d917/nested-counts-c7d917-d2-m2-clean.trace'
        trace = trace_data(path)
        row = self.rows[0]
        validate_trace(row, trace)
        for change in ['empty', 'depth', 'steps', 'gcd', 'inverse']:
            bad = copy.deepcopy(trace)
            if change == 'empty': bad['callback_counts'] = {}
            elif change == 'depth': bad['callback_counts']['3:mul'] = 1
            elif change == 'steps': bad['callback_counts']['2:mul'] += 1
            elif change == 'gcd': bad['operation_counts']['poly_gcd'] += 1
            elif change == 'inverse': bad['callback_counts']['2:inverse_xgcd'] = 0
            with self.assertRaises(ValueError): validate_trace(row, bad)


    def test_retained_derived_outputs(self):
        repo = Path(__file__).resolve().parents[2]
        archive = repo / 'reports/bench-results/real-closure-nested-diagnostics-c7d917'
        manifest = json.loads((archive / 'manifest.json').read_text())
        for name, expected in manifest['files'].items():
            self.assertEqual(hashlib.sha256((archive / name).read_bytes()).hexdigest(), expected, name)
        builder = manifest['rebuild_builder']
        self.assertEqual(hashlib.sha256((archive / builder['file']).read_bytes()).hexdigest(), builder['sha256'])
        self.assertIn(builder['record'], manifest['files'])
        for entry in manifest['derived']:
            self.assertEqual(hashlib.sha256((archive / entry['oracle_file']).read_bytes()).hexdigest(), entry['oracle_sha256'])
            command = list(entry['command'])
            command[0] = sys.executable
            command[1] = str(archive / entry['oracle_file'])
            actual = subprocess.check_output(command, cwd=repo)
            self.assertEqual(actual, (archive / entry['output']).read_bytes(), entry['output'])



class MonicTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        fixture = Path(__file__).resolve().parents[2] / 'conformance-fixtures/HexRealClosure/monic-normalization.jsonl'
        cls.rows = [json.loads(line) for line in fixture.read_text().splitlines()]

    def test_production_values(self):
        self.assertEqual([(r['depth'], r['steps']) for r in self.rows],
                         [(d, m) for d in (1, 2) for m in (2, 4, 8, 16)])
        checked = [verify(row) for row in self.rows]
        verify_pairs(self.rows, checked)
        for result in checked:
            self.assertTrue(result['production_reductions_checked'])
            self.assertTrue(all(degree < 3 for degree in result['stored']['max_degree_by_level']))

    def test_changed_branch_and_family(self):
        for source in self.rows:
            for change in ('flag_type', 'disabled', 'missing', 'family', 'same_roots_scaled_head'):
                with self.subTest(depth=source['depth'], steps=source['steps'], change=change):
                    row = copy.deepcopy(source)
                    expected = 'monic production reduction was not enabled'
                    if change == 'flag_type': row['production_reductions'][0] = 1
                    elif change == 'disabled': row['production_reductions'][0] = False
                    elif change == 'missing': row.pop('production_reductions')
                    elif change == 'family':
                        row['monic'] = False
                        expected = 'different defining polynomial'
                    else:
                        for coefficient in row['heads'][0]: coefficient[0] *= 2
                        expected = 'different defining polynomial'
                    with self.assertRaisesRegex(ValueError, expected): verify(row)

    def test_changed_values_and_selection(self):
        from fractions import Fraction
        from itertools import zip_longest

        def add(left, right, level):
            if level == 0:
                value = Fraction(*left) + Fraction(*right)
                return [value.numerator, value.denominator]
            zero = [0, 1] if level == 1 else []
            result = [add(a, b, level - 1) for a, b in
                      zip_longest(left, right, fillvalue=zero)]
            while result and result[-1] == zero:
                result.pop()
            return result

        for source in self.rows:
            for change in ('value', 'unreduced', 'negative_root'):
                with self.subTest(depth=source['depth'], steps=source['steps'], change=change):
                    row = copy.deepcopy(source)
                    if change == 'value':
                        coefficient = row['value']
                        for _ in range(row['depth']): coefficient = coefficient[0]
                        coefficient[0] += coefficient[1]
                        expected = 'stored value disagrees'
                    elif change == 'unreduced':
                        row['value'] = add(row['value'], row['heads'][-1], row['depth'])
                        expected = 'value was not reduced'
                    else:
                        graph = row['roots'][-1][2]
                        node = graph[2][graph[1]][0]
                        def scalar(n, level):
                            value = [n, 1]
                            for _ in range(level): value = [value] if n else []
                            return value
                        node[2] = [1, scalar(-2, row['depth'] - 1)]
                        node[3] = [1, scalar(0, row['depth'] - 1)]
                        expected = 'different selected-root interval'
                    with self.assertRaisesRegex(ValueError, expected): verify(row)


if __name__ == '__main__':
    unittest.main()
