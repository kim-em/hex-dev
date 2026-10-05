"""Reject altered printed packets, literal types, context fields and observations."""
import copy
import json
from pathlib import Path
import unittest
from scripts.oracle.real_closure_bytes import packet, parse, verify


class ByteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[2]/'conformance-fixtures/HexRealClosure/bytes.jsonl'
        cls.rows = [parse(line) for line in path.read_text().splitlines()]

    def test_actual_packets(self):
        self.assertEqual(verify(self.rows),5)

    def test_packet_mutations(self):
        mutations = [
            lambda d:d.pop(),
            lambda d:d.reverse(),
            lambda d:d[0].update(value_text='['),
            lambda d:d[0].update(value_text=d[0]['value_text'].replace('1 , 3','2 , 3')),
            lambda d:d[1]['value_json'][0].__setitem__(1,1),
            lambda d:d[2]['polynomial_json'][0][2].pop(),
            lambda d:d[3].update(sign=-1),
            lambda d:d[0].update(roundtrip=False),
            lambda d:d[1].update(reconstructed=False),
            lambda d:d[2].update(rejections=7),
            lambda d:d[4].update(unknown_rejected=False),
            lambda d:d[4].update(value_text=d[4]['value_text'].replace('17','18')),
        ]
        for i,mutate in enumerate(mutations):
            with self.subTest(mutation=i):
                rows = copy.deepcopy(self.rows)
                mutate(rows)
                with self.assertRaises(ValueError): verify(rows)
        for field in ['root','stage','unicode']:
            with self.subTest(coupled_change=field):
                rows = copy.deepcopy(self.rows)
                index = 4 if field == 'unicode' else 1
                value = rows[index]['value_json']
                if field == 'root': value[0][2][0][1][0][1] = 7
                elif field == 'stage': value[0][1] = 1
                else: value[0][0][0][1] = 18
                rows[index]['value_text'] = json.dumps(value,ensure_ascii=False)
                if field != 'unicode':
                    rows[index]['polynomial_json'][0] = copy.deepcopy(value[0])
                    rows[index]['polynomial_text'] = json.dumps(
                        rows[index]['polynomial_json'],ensure_ascii=False)
                reason = {
                    'root':'reducible selected predecessor changed',
                    'stage':'lost context stage or root',
                    'unicode':'Unicode or provider version changed',
                }[field]
                with self.assertRaisesRegex(ValueError,reason): verify(rows)

    def test_json_literal_types_and_duplicate_fields(self):
        with self.assertRaises(ValueError): packet('[[[],0,[]],[0,true,3]]',[[[],0,[]],[0,1,3]])
        for root in [False,True]:
            with self.subTest(coupled_boolean=root):
                rows = copy.deepcopy(self.rows)
                index = 1 if root else 0
                value = rows[index]['value_json']
                if root:
                    value[0][2][0][1][-1][1] = True
                    rows[index]['polynomial_json'][0] = copy.deepcopy(value[0])
                    rows[index]['polynomial_text'] = json.dumps(rows[index]['polynomial_json'])
                    reason = 'reducible selected predecessor changed'
                else:
                    value[1][1] = True
                    reason = 'wrong rational example'
                rows[index]['value_text'] = json.dumps(value)
                with self.assertRaisesRegex(ValueError,reason): verify(rows)
        for text in ['1.0','1e2','NaN','{"case":"a","case":"b"}']:
            with self.subTest(text=text), self.assertRaises(ValueError): parse(text)


if __name__ == '__main__':
    unittest.main()
