"""Counter regions and functional packet bindings fail closed."""
from copy import deepcopy
import json
import unittest

from scripts.bench.meti_counts import KINDS, check_packet, parse_record


def record():
    counts = dict.fromkeys(KINDS, 0)
    counts.update(yun_loop_tests=2, signed_chains=1)
    return dict(schema=1, valid=True, counts=counts, lean_nat_gcd=5, gmp_gcd=5, gmp_gcdext=0)


def events(value):
    return 'METI BEGIN\nMETI END\nMETI COUNTERS ' + json.dumps(value) + '\n'


class CaptureTests(unittest.TestCase):
    def test_completed_region(self):
        value = record()
        self.assertEqual(parse_record('unrelated diagnostic\n' + events(value)), value)

    def test_incomplete_duplicate_and_invalid_regions(self):
        raw = events(record())
        for text in [raw.replace('METI END\n', ''), 'METI BEGIN\n' + raw,
                     raw + raw, raw.replace('METI END', 'METI END extra')]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_record(text)
        bad = record()
        bad['valid'] = False
        with self.assertRaises(ValueError):
            parse_record(events(bad))

    def test_invalid_counts_and_missing_categories(self):
        for invalid in [-1, 2**64, True, 1.25, '1']:
            bad = record()
            bad['counts']['poly_gcd'] = invalid
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                parse_record(events(bad))
        bad = record()
        del bad['counts']['bisection_nodes']
        with self.assertRaises(ValueError):
            parse_record(events(bad))
        bad = record()
        bad['counts']['yun_loop_tests'] = 0
        with self.assertRaises(ValueError):
            parse_record(events(bad))

    def test_duplicate_json_keys(self):
        raw = events(record()).replace('"valid": true', '"valid": false, "valid": true')
        with self.assertRaisesRegex(ValueError, 'duplicate counter key'):
            parse_record(raw)

    def test_packet_identity_and_success_flags(self):
        packet = dict(schema=1, workload='metitarski-degree-ladder', degree=3,
                      root_count=1, multiplicity=1, equation_sign=0,
                      first_replay=True, root_replay=True, root=['sentinel'])
        expected = json.dumps(packet) + '\n'
        self.assertEqual(check_packet(expected, expected, 3), packet)
        changed = deepcopy(packet)
        changed['root'] = ['different selected root']
        with self.assertRaisesRegex(ValueError, 'differs'):
            check_packet(json.dumps(changed) + '\n', expected, 3)
        for field, invalid in [('degree', 5), ('first_replay', False), ('root_replay', 1),
                               ('schema', True), ('root_count', True),
                               ('multiplicity', True), ('equation_sign', False)]:
            changed = dict(packet, **{field: invalid})
            raw = json.dumps(changed) + '\n'
            with self.subTest(field=field), self.assertRaises(ValueError):
                check_packet(raw, raw, 3)


if __name__ == '__main__':
    unittest.main()
