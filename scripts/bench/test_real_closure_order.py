"""Reject invalid complete-root batches using a retained real LeanBench export."""
import copy
import json
from pathlib import Path
import tarfile
import unittest
from scripts.bench.fixed_conversion_paired import validate_tower_row, check_tower_cohort


class BatchTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        archive=Path(__file__).resolve().parents[2]/'reports/bench-results/real-closure-distinct/capture.tar.gz'
        with tarfile.open(archive) as source:
            member=next(m for m in source.getmembers() if m.name=='00-Quadratic8-generic.json')
            cls.row=json.load(source.extractfile(member))['results'][0]
        cls.target=cls.row['function']
        cls.commit=cls.row['env']['git_commit']

    def reject(self, change):
        row=copy.deepcopy(self.row)
        change(row)
        with self.assertRaises(ValueError):
            validate_tower_row(row,self.target,self.commit)

    def test_retained_complete_batch(self):
        p=self.row['points'][0]
        self.assertEqual(validate_tower_row(self.row,self.target,self.commit),
                         p['total_nanos']/p['inner_repeats']/1e6)

    def test_wrong_source(self):
        with self.assertRaises(ValueError):
            validate_tower_row(self.row,self.target,'other')

    def test_wrong_function(self):
        with self.assertRaises(ValueError):
            validate_tower_row(self.row,'other',self.commit)

    def test_dirty_source(self):
        self.reject(lambda r:r['env'].__setitem__('git_dirty',True))

    def test_wrong_consumer(self):
        self.reject(lambda r:r.__setitem__('observed_hash','0x0'))

    def test_failed_expected_hash(self):
        self.reject(lambda r:r['expected_hash_check'].__setitem__('status','mismatch'))

    def test_failed_point_hash(self):
        self.reject(lambda r:r['points'][0].__setitem__('result_hash','0x0'))

    def test_incomplete_batch(self):
        self.reject(lambda r:r['points'][0].__setitem__('inner_repeats',0))

    def test_boolean_duration(self):
        self.reject(lambda r:r['points'][0].__setitem__('total_nanos',True))

    def test_truncated_arm(self):
        self.reject(lambda r:r.__setitem__('budget_truncated',True))

    def test_different_floor(self):
        self.reject(lambda r:r['config'].__setitem__('min_total_seconds',.05))

    def test_missing_warmup(self):
        self.reject(lambda r:r['config'].__setitem__('warmup_first_iter',False))


class CohortTests(unittest.TestCase):
    def setUp(self):
        keys=['.lake/build/ir/HexRealClosure/'+name+'.c.o.export'
              for name in ('RootOrder','Trivial','TrivialMeasurements')]
        self.sources={arm:dict(compiler='cc',linked_objects={
            key:dict(sha256=arm+key,c_sha256=arm+key,compiler='cc',command=['cc','-O3',key])
            for key in keys}) for arm in ('Before','After')}
        for source in self.sources.values():
            source['linked_objects']['unchanged']=dict(sha256='same',c_sha256='same')

    def test_only_registered_generated_changes(self):
        check_tower_cohort(self.sources)

    def test_unchanged_source_compiler_confound(self):
        self.sources['After']['linked_objects']['unchanged']['sha256']='different'
        with self.assertRaises(ValueError):
            check_tower_cohort(self.sources)

    def test_changed_compiler(self):
        key=next(iter(self.sources['After']['linked_objects']))
        self.sources['After']['linked_objects'][key]['command'][0]='other'
        with self.assertRaises(ValueError):
            check_tower_cohort(self.sources)

    def test_unregistered_generated_change(self):
        self.sources['After']['linked_objects']['unchanged']['c_sha256']='different'
        with self.assertRaises(ValueError):
            check_tower_cohort(self.sources)


if __name__=='__main__':
    unittest.main()
