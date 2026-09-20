"""Adversarial tests for the exact named-constant oracle and fixture schema."""
from copy import deepcopy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import FixtureError, _validate_fixture
from interval_constants import validate


class ConstantsOracleTests(unittest.TestCase):
    def setUp(self):
        # S_4 = 8/3, R_4 = 5/96. Outward rounding on quarters is [5/2,11/4].
        self.case = dict(kind='interval-constant-v1', lib='HexInterval', case='e/0',
                         source='exp-one-taylor-v1', bits=0, order=4,
                         center=[8, 3], radius=[5, 96], lower=[5, 2], upper=[11, 4],
                         accepted=True)

    def test_exact_case(self):
        _validate_fixture(self.case)
        validate(self.case)

    def test_reject_changed_results(self):
        for field, value in [('center', [0, 1]), ('radius', [0, 1]),
                             ('lower', [11, 4]), ('upper', [5, 2]),
                             ('accepted', False), ('bits', 8),
                             ('source', 'pi-machin-v1')]:
            with self.subTest(field=field):
                case = deepcopy(self.case)
                case[field] = value
                with self.assertRaises(AssertionError):
                    validate(case)

    def test_reject_bad_schema(self):
        for field, value in [('order', 0), ('bits', -1), ('bits', True),
                             ('center', [16, 6]), ('radius', [1, 0]),
                             ('source', 'pi-machin-v2'), ('accepted', 1)]:
            with self.subTest(field=field):
                case = deepcopy(self.case)
                case[field] = value
                with self.assertRaises(FixtureError):
                    _validate_fixture(case)


if __name__ == '__main__':
    unittest.main()
