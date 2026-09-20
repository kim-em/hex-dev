"""Crossover evidence belongs to the entry encoding actually measured."""
import unittest
from scripts.bench.det_packed_table import selected_tables
from scripts.bench.det_packed_report import audit_dispatch


class EntryEncodingTests(unittest.TestCase):
    def record(self):
        key = [32, 1, 4, 1, 2]
        record = dict(stage='forced', schedule_complete=True, sources_unchanged=True,
            subset=False, summary={}, classification={}, samples=[])
        for stem, entries, packed in [('Tree', 'tree', 1), ('List', 'list', 3)]:
            record['summary'][stem] = dict(arms={
                'Lists': dict(median_delta_ns=2), 'Packed': dict(median_delta_ns=packed)})
            record['classification'][stem] = dict(classification='eligible', entries=entries,
                selection=dict(products=[dict(key=key)]))
            for _ in range(6):
                for arm, route in [('Lists', 'term-list'), ('Packed', 'packed/plain')]:
                    record['samples'].append(dict(stem=stem, arm=arm,
                        routes=[dict(route=route, entries=entries if arm == 'Packed' else 'list')]))
        return record

    def test_numeric_collision_does_not_transfer_evidence(self):
        winners, tables = selected_tables(self.record())
        self.assertEqual(winners, ['Tree'])
        self.assertEqual(tables['list'], [])
        self.assertEqual(tables['tree'], [(32, 1, 4, 1, 2)])
        record = self.record()
        record['samples'] = [dict(stem='List', arm='Dispatch', candidate=dict(state='complete'),
            routes=[dict(route='term-list')])]
        audit_dispatch(record, dict(keys_by_entries=tables))
        record['samples'][0]['routes'] = [dict(route='packed/plain', products=[dict(key='{ packedBits := 32, leftSupport := 1, rightSize := 4, resultSupport := 1, inner := 2 }')])]
        with self.assertRaises(ValueError):
            audit_dispatch(record, dict(keys_by_entries=tables))

    def test_wrong_encoding_cannot_fit_tree_table(self):
        record = self.record()
        record['samples'][1]['routes'][0]['entries'] = 'list'
        with self.assertRaisesRegex(ValueError, 'entry encoding'):
            selected_tables(record)

    def test_incomplete_arm_cannot_fit_table(self):
        record = self.record()
        record['samples'].pop(1)
        with self.assertRaisesRegex(ValueError, 'six actual'):
            selected_tables(record)


if __name__ == '__main__':
    unittest.main()
