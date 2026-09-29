"""Reject false tables and context substitutions in deep coefficient fixtures."""
import copy
import json
import unittest
from unittest import mock
import contextlib
import io

from scripts.oracle import sign_det_nested_z3 as oracle
from scripts.oracle.common import OracleMismatch


class NestedFieldsOracle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        oracle.check_version()
        cls.records = [json.loads(line) for line in oracle.DEFAULT_FIXTURE.read_text().splitlines()]

    def reject(self, change):
        record = copy.deepcopy(self.records[-1])
        change(record)
        with self.assertRaises(OracleMismatch):
            oracle.check_record(record)

    def test_actual_four_levels(self):
        self.assertEqual([r['case'] for r in self.records], oracle.CASES)
        for record in self.records:
            oracle.check_record(record)

    def test_omitted_pattern_with_preserved_total(self):
        self.reject(lambda r: r['value']['result']['reduced'].update(table=[[[1, 0], 2]]))

    def test_wrong_sign_and_non_integer_count(self):
        self.reject(lambda r: r['value']['result']['reduced']['table'][1].__setitem__(0, [1, 1]))
        self.reject(lambda r: r['value']['result']['reduced']['table'][1].__setitem__(1, True))

    def test_foreign_reordered_and_shallower_contexts(self):
        for key, value in [('id', 10378), ('levels', ['epsilon4','epsilon3','epsilon2','epsilon1']),
                           ('levels', ['epsilon1','epsilon2','epsilon3'])]:
            self.reject(lambda r: r['value']['coefficientContext'].__setitem__(key, value))

    def test_changed_head_and_queries(self):
        self.reject(lambda r: r['value']['result']['input']['head'].__setitem__(0, r['value']['result']['input']['head'][2]))
        self.reject(lambda r: r['value']['result']['input']['queries'].__setitem__(1, r['value']['result']['input']['queries'][0]))

    def test_replay_rejections_are_required(self):
        for name in ['reduced','direct']:
            for key in ['foreignContextReplay','staleChildReplay','copiedHeadReplay','missingSupportReplay']:
                self.reject(lambda r: r['value']['result'][name].__setitem__(key, True))
            self.reject(lambda r: r['value']['result'][name].__setitem__('leafLayout', False))
        self.reject(lambda r: r['value']['result'].__setitem__('foreignChildValid', False))

    def test_reversed_actual_field_order_changes_the_answer(self):
        record = self.records[-1]
        field = oracle.RCF(record['value']['coefficientContext'], maximum_depth=4)
        field.levels.reverse()
        raw = record['value']['result']['input']
        table = field.table({**raw, 'lower': '-inf', 'upper': '+inf'})
        self.assertEqual([[e['signs'], e['count']] for e in table],
                         [[[-1, 0], 1], [[1, 1], 1]])
        self.assertNotEqual([[e['signs'], e['count']] for e in table],
                            record['value']['result']['reduced']['table'])

    def test_infinitely_large_first_generator_changes_the_answer(self):
        record = self.records[0]
        field = oracle.RCF(record['value']['coefficientContext'], maximum_depth=4)
        field.levels[0] = field.one.__div__(field.levels[0])
        raw = record['value']['result']['input']
        table = field.table({**raw, 'lower': '-inf', 'upper': '+inf'})
        self.assertEqual([[e['signs'], e['count']] for e in table],
                         [[[-1, 0], 1], [[1, 1], 1]])
        self.assertNotEqual([[e['signs'], e['count']] for e in table],
                            record['value']['result']['reduced']['table'])

    def test_stdin_and_explicit_fixture_selection(self):
        for args, source in [([], None), (['--check'], oracle.DEFAULT_FIXTURE)]:
            with mock.patch('sys.argv', ['oracle', *args]), \
                 mock.patch.object(oracle, 'read_fixtures', return_value=self.records) as read, \
                 mock.patch.object(oracle, 'check_record'), \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(oracle.main(), 0)
                read.assert_called_once_with(source)

    def test_wrong_case_depth_and_generator_sign(self):
        self.reject(lambda r: r['value'].__setitem__('extensionDepth', True))
        self.reject(lambda r: r.__setitem__('case', 'nested-field/depth-3'))
        self.reject(lambda r: r['value']['result'].__setitem__('generatorSign', -1))
        self.reject(lambda r: r['value'].__setitem__('zeroDomainRejected', False))


if __name__ == '__main__':
    unittest.main()
