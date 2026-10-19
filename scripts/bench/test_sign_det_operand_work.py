"""Actual independent root checks and adversarial trace/archive checks."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from scripts.bench.sign_det_operand_archive import ROOT, validate
from scripts.bench.sign_det_operand_work import validate_joint, validate_interacting
from scripts.oracle.common import OracleMismatch
from scripts.oracle.sign_det_nested_z3 import check_record


class OperandWorkTests(unittest.TestCase):
    def mutate(self, source, checker, edit):
        rows=[json.loads(s) for s in Path(source).read_text().splitlines()]
        edit(rows)
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'observations.jsonl'
            p.write_text(''.join(json.dumps(r)+'\n' for r in rows))
            with self.assertRaises((ValueError,KeyError,TypeError,ArithmeticError,OracleMismatch)):
                checker(p)

    def test_actual_sources_and_answers(self):
        self.assertEqual(len(validate()),24)
        for arm in ('A','B'):
            self.assertEqual(len(validate_interacting(ROOT/arm/'observations.jsonl')),9)
            self.assertEqual(len(validate_joint(ROOT/arm/'joint.jsonl')),3)
        records=[json.loads(s) for s in (ROOT/'B/conformance.jsonl').read_text().splitlines()]
        self.assertEqual(len(records),4)
        for r in records: check_record(r)

    def test_joint_subject_mutations(self):
        p=ROOT/'B/joint.jsonl'
        for key,value in [('context',10377),('order','lt'),('leftSigns',[True]*6),
                          ('factor',[[1,1]]),('commonHead',[[1,1]])]:
            with self.subTest(key=key):
                self.mutate(p,validate_joint,lambda rows,k=key,v=value:rows[0]['result'].__setitem__(k,v))

    def test_interacting_subject_mutations(self):
        p=ROOT/'B/observations.jsonl'
        for key,value in [('context',10377),('lower','posInf'),('generator',[0,1]),
                          ('entries',[[[-1,-1],2]]),('entries',[[[-1,-1],1],[[1,-1],1]])]:
            with self.subTest(key=key):
                self.mutate(p,validate_interacting,lambda rows,k=key,v=value:rows[0]['result'].__setitem__(k,v))
        for key,value in [('anchor',[0,1]),('head',[]),('queryPolynomials',[]),
                          ('upper','negInf'),('standardReplayAccepted',False),('mode','wrong')]:
            with self.subTest(deep=key):
                self.mutate(p,validate_interacting,lambda rows,k=key,v=value:rows[8]['result'].__setitem__(k,v))

    def test_observation_mutations(self):
        for filename,checker,key,value in [('joint.jsonl',validate_joint,'coefficientCalls',1),
                    ('joint.jsonl',validate_joint,'maxNormalizedBits',1),
                    ('observations.jsonl',validate_interacting,'maxRationalSlots',1),
                    ('observations.jsonl',validate_interacting,'maxNormalizedRatBits',1),
                    ('observations.jsonl',validate_interacting,'operationCalls',[-1]*8)]:
            with self.subTest(key=key):
                self.mutate(ROOT/'B'/filename,checker,lambda rows,k=key,v=value:rows[0].__setitem__(k,v))

    def test_archive_tampering(self):
        for relative in ('B/observations.jsonl','A/source.patch','paired/samples.jsonl',
                         'paired/0-depthOne-A.json'):
            with self.subTest(path=relative), tempfile.TemporaryDirectory() as folder:
                root=Path(folder)/'archive'; shutil.copytree(ROOT,root)
                with (root/relative).open('ab') as f: f.write(b' ')
                with self.assertRaises(ValueError): validate(root)


if __name__=='__main__': unittest.main()
