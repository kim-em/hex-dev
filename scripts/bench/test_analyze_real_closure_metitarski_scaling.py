"""Regression checks for retained batches, caps, input binding and archives."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from scripts.bench.analyze_real_closure_metitarski_scaling import (
    DEGREES, FUNCTION, SOURCES, digest, summarize)


class ScalingCaptureTests(unittest.TestCase):
    def prepare(self, folder):
        def put(name, value):
            path = folder/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(value))
        env = dict(git_commit='a'*40, git_dirty=False)
        points = []
        for trial in range(6):
            for degree in DEGREES:
                status = 'killed_at_cap' if degree == 9 and trial == 2 else 'ok'
                points.append(dict(trial_index=trial, param=degree, status=status,
                                   result_hash='0x1' if status=='ok' else None,
                                   below_signal_floor=False,
                                   inner_repeats=2 if status=='ok' else 0,
                                   total_nanos=300000000 if status=='ok' else 0,
                                   per_call_nanos=150000000.0 if status=='ok' else 0.0))
        result = dict(kind='parametric', function=FUNCTION, budget_truncated=False,
                      config=dict(param_schedule=dict(kind='custom', params=DEGREES),
                                  outer_trials=6, target_inner_nanos=500000000,
                                  max_seconds_per_call=120, signal_floor_multiplier=1),
                      env=env, points=points, verdict='inconclusive', slope=None,
                      verdict_dropped_leading=0)
        put('measurements.json', dict(export_schema_version=1, env=env, results=[result]))
        functional = []
        for degree in DEGREES:
            value = dict(degree=degree, head=[degree], first_coefficients=[1,2], first=[degree,1])
            put(f'functional-{degree}.json', value)
            put(f'measured-{degree}.json', value)
            put(f'oracle-{degree}.json', dict(degree=degree, real_roots=1,
                                             multiplicity=1, head_bytes=10,
                                             descriptor_bytes=100))
            functional.append(dict(degree=degree, fixture=f'functional-{degree}.json',
                                   measured_input=f'measured-{degree}.json',
                                   oracle=f'oracle-{degree}.json'))
        for name in SOURCES:
            path = folder/'sources'/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text('frozen source '+name)
        for name in ['hexrealclosure_bench', 'hexrealclosure_phase4']:
            (folder/name).write_bytes(name.encode())
        record = dict(schema=1, status='completed', degrees=DEGREES, trials=6,
                      dirty=False, affinity=[1], cpu=1, commit=env['git_commit'],
                      oracle_version='0.9.0 3.6.0',
                      commands=[dict(argv=['hexrealclosure_bench','run',FUNCTION],
                                     exit_code=0, acceptable_exit_codes=[0,2])], functional=functional,
                      source_hashes={name:digest(folder/'sources'/name) for name in SOURCES})
        record['artifacts'] = {str(p.relative_to(folder)):digest(p)
                               for p in folder.rglob('*') if p.is_file()}
        for name in ['hexrealclosure_bench', 'hexrealclosure_phase4']:
            record[name+'_sha256'] = record['artifacts'][name]
        put('manifest.json', record)
        return record

    def reseal(self, folder, record, name):
        record['artifacts'][name] = digest(folder/name)
        (folder/'manifest.json').write_text(json.dumps(record))

    def test_short_batch_and_cap_are_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            self.prepare(folder)
            result = summarize(folder)
            self.assertEqual((result['attempts'], result['completed_samples']), (24,23))
            self.assertEqual(result['rows'][0]['median_ns'], 150000000)
            self.assertEqual(result['rows'][0]['batches'][0]['total_nanos'], 300000000)
            self.assertEqual(result['rows'][-1]['failures'][0]['status'], 'killed_at_cap')
            self.assertEqual(result['rows'][-1]['completed_trials'], 5)

    def test_signal_floor_is_retained(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            record = self.prepare(folder)
            document = json.loads((folder/'measurements.json').read_text())
            document['results'][0]['points'][0]['below_signal_floor'] = True
            (folder/'measurements.json').write_text(json.dumps(document))
            self.reseal(folder, record, 'measurements.json')
            result = summarize(folder)
            self.assertEqual(result['completed_samples'], 23)
            self.assertTrue(result['rows'][0]['batches'][0]['below_signal_floor'])

    def test_all_failures_and_harness_exit_two(self):
        for status in ['killed_at_cap', 'timed_out', 'error']:
            with self.subTest(status=status), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                record = self.prepare(folder)
                document = json.loads((folder/'measurements.json').read_text())
                for point in document['results'][0]['points']:
                    point.update(status=status, inner_repeats=0, total_nanos=0,
                                 per_call_nanos=0.0, result_hash=None)
                (folder/'measurements.json').write_text(json.dumps(document))
                record['commands'][0]['exit_code'] = 2
                self.reseal(folder, record, 'measurements.json')
                result = summarize(folder)
                self.assertEqual(result['completed_samples'], 0)
                self.assertTrue(all(r['median_ns'] is None and len(r['failures'])==6
                                    for r in result['rows']))

    def test_semantic_changes_despite_matching_artifact_hashes(self):
        changes = [
            ('measurements.json', lambda d:d['results'][0]['points'].pop()),
            ('measurements.json', lambda d:d['results'][0]['points'][0].update(status='capped')),
            ('measurements.json', lambda d:d['results'][0]['points'][0].update(total_nanos=0)),
            ('measurements.json', lambda d:d['results'][0]['points'][0].update(result_hash='0x0')),
            ('measurements.json', lambda d:d['results'][0]['points'][0].update(per_call_nanos=1)),
            ('measured-9.json', lambda d:d.update(head=[7])),
            ('measured-9.json', lambda d:d.update(first=[7,1])),
            ('oracle-9.json', lambda d:d.update(multiplicity=2)),
        ]
        for name, mutate in changes:
            with self.subTest(file=name, mutation=mutate), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                record = self.prepare(folder)
                value = json.loads((folder/name).read_text())
                mutate(value)
                (folder/name).write_text(json.dumps(value))
                self.reseal(folder, record, name)
                with self.assertRaises(ValueError): summarize(folder)

    def test_binary_and_source_identity(self):
        for field in ['hexrealclosure_bench_sha256', 'source_hashes']:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                record = self.prepare(folder)
                record[field] = '0'*64 if field.endswith('sha256') else {}
                (folder/'manifest.json').write_text(json.dumps(record))
                with self.assertRaises(ValueError): summarize(folder)

    def test_archive_and_inventory_mutations(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            record = self.prepare(folder)
            omitted = {}
            for name in ['hexrealclosure_bench', 'hexrealclosure_phase4']:
                omitted[name] = record['artifacts'][name]
                (folder/name).unlink()
            (folder/'README.md').write_text('Descriptive test report')
            index = dict(schema='metitarski-scaling-v1', commit=record['commit'],
                         omitted_snapshots=omitted,
                         files={str(p.relative_to(folder)):digest(p)
                                for p in folder.rglob('*') if p.is_file() and p.name!='README.md'})
            (folder/'archive.json').write_text(json.dumps(index))
            self.assertEqual(summarize(folder, archive=True)['completed_samples'], 23)
            (folder/'extra.json').write_text('{}')
            with self.assertRaises(ValueError): summarize(folder, archive=True)
            (folder/'extra.json').unlink()
            changed = copy.deepcopy(index)
            changed['omitted_snapshots']['hexrealclosure_bench'] = '0'*64
            (folder/'archive.json').write_text(json.dumps(changed))
            with self.assertRaises(ValueError): summarize(folder, archive=True)
            (folder/'archive.json').write_text(json.dumps(index))
            (folder/'measured-9.json').write_text('{}')
            with self.assertRaises(ValueError): summarize(folder, archive=True)


if __name__ == '__main__':
    unittest.main()
