"""Audit retained complete-root batches and untimed sort diagnostics."""
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


class SortInventoryTests(unittest.TestCase):
    def setUp(self):
        from scripts.bench.analyze_real_closure_order import analyze_sort_rows
        self.check=analyze_sort_rows
        self.report=Path(__file__).resolve().parents[2]/'reports/bench-results/real-closure-thom-order'
        self.rows=[json.loads(line) for line in (self.report/'sort.jsonl').read_text().splitlines()]

    def test_retained_sort_and_selection(self):
        from scripts.bench.analyze_real_closure_order import analyze_sort_inventory
        expected=json.loads((self.report/'sort-analysis.json').read_text())
        self.assertEqual(analyze_sort_inventory(self.report),expected)
        self.assertEqual([r['comparisons'] for r in expected],[1,6,12,23,1,6,14,25])
        self.assertEqual([r['routes']['full'] for r in expected],[0,0,0,0,0,0,1,3])

    def test_retained_interval_inventory(self):
        directory=self.report.parent/'real-closure-interval-order'
        metadata=json.loads((directory/'source.json').read_text())
        self.assertEqual(metadata['comparison_schema'],2)
        self.assertEqual(metadata['exit_code'],0)
        for name,expected in metadata['files'].items():
            self.assertEqual(Path(name).name,name)
            data=(directory/name).read_bytes()
            self.assertEqual(len(data),expected['bytes'])
            self.assertEqual(hashlib.sha256(data).hexdigest(),expected['sha256'])
        for name,expected in metadata['source_git_blobs'].items():
            data=(directory/name).read_bytes()
            self.assertEqual(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),expected)
        rows=[json.loads(line) for line in (directory/'sort.jsonl').read_text().splitlines()]
        self.assertTrue(all(row['comparison_schema']==2 for row in rows))
        result=self.check(rows)
        self.assertEqual(result,json.loads((directory/'sort-analysis.json').read_text()))
        self.assertEqual(result[-1]['routes']['interval'],22)
        self.assertEqual((directory/'sort.stderr').read_bytes(),b'')

    def test_changed_route(self):
        self.rows[-1]['comparisons'][0]['route']='linear'
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_changed_order(self):
        event=self.rows[-1]['comparisons'][0]
        event['order']='gt' if event['order']=='lt' else 'lt'
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_omitted_comparison(self):
        self.rows[-1]['comparisons'].pop()
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_changed_assembly_index(self):
        self.rows[-1]['assembled'][0]['index']=1
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_duplicate_output_index(self):
        self.rows[-1]['sorted_indices'][0]=self.rows[-1]['sorted_indices'][1]
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_changed_pair(self):
        self.rows[-1]['comparisons'][0]['left']=0
        with self.assertRaises(ValueError): self.check(self.rows)

    def interval_rows(self):
        for row in self.rows:
            row['comparison_schema']=2
            for entry in row['assembled']:
                root=entry['root']
                if 'point' not in root:
                    root.update(lower='negInf',upper='posInf')
        row=self.rows[4]
        row['assembled'][0]['root']['upper']={'finite':[0,1]}
        row['assembled'][1]['root']['lower']={'finite':[0,1]}
        row['comparisons'][0]['route']='interval'
        return row

    def test_interval_route_and_shared_endpoint(self):
        self.interval_rows()
        result=self.check(self.rows)
        self.assertEqual(result[4]['routes']['interval'],1)
        self.assertEqual(result[4]['routes']['common-product'],0)

    def test_missing_interval_endpoint(self):
        row=self.interval_rows()
        del row['assembled'][0]['root']['lower']
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_invalid_interval_endpoint(self):
        row=self.interval_rows()
        row['assembled'][0]['root']['upper']['finite'][1]=0
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_overlap_cannot_claim_interval_route(self):
        row=self.interval_rows()
        row['assembled'][0]['root']['upper']={'finite':[1,1]}
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_interval_cannot_claim_common_product(self):
        row=self.interval_rows()
        row['comparisons'][0]['route']='common-product'
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_reversed_production_order_rejected(self):
        row=self.interval_rows()
        row['sorted_indices']=[1,0]
        row['comparisons'][0]['order']='gt'
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_reverse_interval_direction(self):
        row=self.interval_rows()
        row['assembled'][0]['root'].update(lower={'finite':[0,1]},upper='posInf')
        row['assembled'][1]['root'].update(lower='negInf',upper={'finite':[0,1]})
        row['sorted_indices']=[1,0]
        row['comparisons'][0]['order']='gt'
        self.assertEqual(self.check(self.rows)[4]['routes']['interval'],1)

    def test_mixed_comparison_schemas(self):
        self.interval_rows()
        del self.rows[0]['comparison_schema']
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_empty_interval(self):
        row=self.interval_rows()
        row['assembled'][0]['root']['lower']={'finite':[0,1]}
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_wrong_infinite_endpoint_side(self):
        row=self.interval_rows()
        row['assembled'][0]['root']['lower']='posInf'
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_noncanonical_endpoint(self):
        row=self.interval_rows()
        row['assembled'][0]['root']['upper']={'finite':[0,2]}
        with self.assertRaises(ValueError): self.check(self.rows)

    def test_unknown_comparison_schema(self):
        self.rows[0]['comparison_schema']=True
        with self.assertRaises(ValueError): self.check(self.rows)


    def reject_inventory(self, mutate):
        import shutil
        from scripts.bench.analyze_real_closure_order import analyze_sort_inventory
        with tempfile.TemporaryDirectory() as temporary:
            directory=Path(temporary)
            names={'sort-source.json','selection-source.json'}
            for name in tuple(names):
                names.update(json.loads((self.report/name).read_text())['files'])
            for name in names:
                shutil.copy2(self.report/name,directory/name)
            mutate(directory)
            with self.assertRaises(ValueError): analyze_sort_inventory(directory)

    @staticmethod
    def reseal(directory, metadata, name):
        path=directory/metadata
        data=json.loads(path.read_text())
        data['files'][name]=hashlib.sha256((directory/name).read_bytes()).hexdigest()
        path.write_text(json.dumps(data))

    def test_inventory_artifact_digest(self):
        self.reject_inventory(lambda directory:(directory/'sort.jsonl').write_text('changed'))

    def test_inventory_git_blob(self):
        def change(directory):
            path=directory/'sort-benchmark.lean.txt'
            path.write_text(path.read_text()+'\n')
            self.reseal(directory,'sort-source.json',path.name)
        self.reject_inventory(change)

    def test_inventory_stdout_binding(self):
        def change(directory):
            path=directory/'sort-launcher.stdout'
            path.write_text(path.read_text()+'\n')
            self.reseal(directory,'sort-source.json',path.name)
        self.reject_inventory(change)

    def test_selection_artifact_digest(self):
        self.reject_inventory(lambda directory:(directory/'selection.jsonl').write_text('changed'))

    def test_selection_descriptor_binding(self):
        def change(directory):
            path=directory/'selection.jsonl'
            rows=[json.loads(line) for line in path.read_text().splitlines()]
            rows[0]['descriptors'][0]['head'][0][0]+=1
            path.write_text('\n'.join(json.dumps(row) for row in rows)+'\n')
            self.reseal(directory,'selection-source.json',path.name)
        self.reject_inventory(change)


if __name__=='__main__':
    unittest.main()
