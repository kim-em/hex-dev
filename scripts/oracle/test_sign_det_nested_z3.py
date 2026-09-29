"""Reject false tables and context substitutions in deep coefficient fixtures."""
import copy
import json
import unittest

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
        self.reject(lambda r: r['value'].update(table=[[[1, 0], 2]]))

    def test_wrong_sign_and_non_integer_count(self):
        self.reject(lambda r: r['value']['table'][1].__setitem__(0, [1, 1]))
        self.reject(lambda r: r['value']['table'][1].__setitem__(1, True))

    def test_foreign_reordered_and_shallower_contexts(self):
        for key, value in [('id', 10378), ('levels', ['epsilon4','epsilon3','epsilon2','epsilon1']),
                           ('levels', ['epsilon1','epsilon2','epsilon3'])]:
            self.reject(lambda r: r['value']['input']['coefficientContext'].__setitem__(key, value))

    def test_changed_head_and_queries(self):
        self.reject(lambda r: r['value']['input']['head'].__setitem__(0, r['value']['input']['head'][2]))
        self.reject(lambda r: r['value']['input']['queries'].__setitem__(1, r['value']['input']['queries'][0]))

    def test_replay_rejections_are_required(self):
        for key in ['reduced','unreduced','fullReference','foreignContextRejected','staleChildRejected']:
            self.reject(lambda r: r['value'].__setitem__(key, False))

    def test_wrong_dimensions_or_case_depth(self):
        for key, value in [('extensionDepth', True), ('headDegree', 2.0), ('queries', 3)]:
            self.reject(lambda r: r['value'].__setitem__(key, value))
        self.reject(lambda r: r.__setitem__('case', 'nested-field/depth-3'))


if __name__ == '__main__':
    unittest.main()
