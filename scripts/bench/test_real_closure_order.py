"""Reject invalid complete-root batches using a retained real LeanBench export."""
import copy
import json
import hashlib
import tempfile
from pathlib import Path
import tarfile
import unittest
from scripts.bench.fixed_conversion_paired import validate_tower_row, check_tower_cohort
from scripts.bench.analyze_real_closure_order import analyze


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


class CaptureTests(unittest.TestCase):
    results=Path(__file__).resolve().parents[2]/'reports/bench-results/real-closure-thom-order'

    def setUp(self):
        temporary=tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.directory=Path(temporary.name)
        with tarfile.open(self.results/'capture.tar.gz') as source:
            source.extractall(self.directory,filter='data')
        self.data=json.loads((self.directory/'metadata.json').read_text())

    def save(self):
        (self.directory/'metadata.json').write_text(json.dumps(self.data))

    def reject(self):
        self.save()
        with self.assertRaises(ValueError):
            analyze(self.directory)

    def mutate_export(self,mutate):
        path=self.directory/self.data['arms'][0]['output']
        data=json.loads(path.read_text())
        mutate(data['results'][0])
        path.write_text(json.dumps(data))
        self.data['artifacts'][path.name]=hashlib.sha256(path.read_bytes()).hexdigest()

    def test_reproduce_complete_analysis(self):
        self.assertEqual(analyze(self.directory),json.loads((self.results/'analysis.json').read_text()))

    def test_incomplete_capture(self):
        self.data['arms'].pop()
        self.reject()

    def test_pair_order(self):
        self.data['arms'][0],self.data['arms'][1]=self.data['arms'][1],self.data['arms'][0]
        self.reject()

    def test_wrong_function(self):
        self.mutate_export(lambda row:row.__setitem__('function','other'))
        self.reject()

    def test_wrong_source(self):
        self.mutate_export(lambda row:row['env'].__setitem__('git_commit','other'))
        self.reject()

    def test_changed_consumer_hash(self):
        self.mutate_export(lambda row:row.__setitem__('observed_hash','0x0'))
        self.reject()

    def test_failed_native_arm(self):
        self.data['arms'][0]['exit_code']=2
        self.reject()

    def test_wrong_command(self):
        self.data['arms'][0]['command'][2]='other'
        self.reject()

    def test_wrong_affinity(self):
        self.data['affinity']=[self.data['cpu']+1]
        self.reject()

    def test_changed_source_snapshot(self):
        name='HexRealClosure/RootOrder.lean'
        path=self.directory/('After-'+name.replace('/','-')+'.txt')
        path.write_bytes(path.read_bytes()+b'\n')
        value=hashlib.sha256(path.read_bytes()).hexdigest()
        self.data['artifacts'][path.name]=value
        self.data['sources']['After']['sources'][name]=value
        self.save()
        with self.assertRaisesRegex(ValueError,'differs from Git'):
            analyze(self.directory)

    def test_compiler_cohort(self):
        objects=self.data['sources']['After']['linked_objects']
        key=next(k for k in objects if k.endswith('/RootOrder.c.o.export'))
        objects[key]['command'][0]='other'
        self.reject()

    def test_disconnected_generated_c(self):
        key='.lake/build/ir/HexRealClosure/RootOrder.c.o.export'
        self.data['sources']['After']['linked_objects'][key]['c_sha256']='forged'
        self.reject()

    def test_disconnected_object_identity(self):
        key='.lake/build/ir/HexRealClosure/RootOrder.c.o.export'
        self.data['sources']['After']['linked_objects'][key]['sha256']='forged'
        self.reject()

    def test_disconnected_compiler_command(self):
        key='.lake/build/ir/HexRealClosure/RootOrder.c.o.export'
        for source in self.data['sources'].values():
            source['linked_objects'][key]['command'].append('-other')
        self.reject()

    def test_failed_preparation(self):
        self.data['sources']['Before']['commands'][0]['exit_code']=1
        self.reject()

    def test_wrong_binary_identity(self):
        self.data['sources']['Before']['binaries']['hexrealclosure_trivial_bench']['sha256']='other'
        self.reject()

    def test_oracle_coverage(self):
        name='Before-oracle.stdout.txt'
        path=self.directory/name
        data=json.loads(path.read_text());data['verified_arms']=8
        path.write_text(json.dumps(data))
        value=hashlib.sha256(path.read_bytes()).hexdigest()
        self.data['artifacts'][name]=value
        self.data['sources']['Before']['artifacts']['oracle.stdout.txt']=value
        self.reject()


if __name__=='__main__':
    unittest.main()
