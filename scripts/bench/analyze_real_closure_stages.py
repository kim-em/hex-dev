"""Validate and summarize the complete fixed-stage capture."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import statistics

STAGES = ('runYun', 'runAssembly', 'runRoots', 'runNativeRoots')


def analyze(directory: Path) -> dict:
    metadata = json.loads((directory / 'metadata.json').read_text())
    # lean-bench serializes the official toolchain tag without its leading v.
    expected_toolchain = metadata['lean_toolchain'].replace(
        'leanprover/lean4:v', 'leanprover/lean4:', 1)
    if metadata['rounds'] != 6 or tuple(metadata['trial_major_order']) != STAGES:
        raise ValueError('changed registered schedule')
    expected = [(trial, stage) for trial in range(6) for stage in STAGES]
    observed = [(item['trial'], item['stage']) for item in metadata['observations']]
    if observed != expected or any(item['exit_code'] for item in metadata['observations']):
        raise ValueError('incomplete or failed capture')
    summary = {}
    for stage in STAGES:
        values, batches = [], []
        for trial in range(6):
            export = json.loads((directory / f'{trial:02d}-{stage}.json').read_text())
            if len(export['results']) != 1:
                raise ValueError('unexpected result count')
            result = export['results'][0]
            environment = export['env']
            if (result['env'] != environment or environment['git_commit'] != metadata['source']
                    or environment['git_dirty'] is not False
                    or environment['exe_name'] != 'hexrealclosure_bench'
                    or environment['hostname'] != metadata['host']
                    or environment['lean_toolchain'] != expected_toolchain):
                raise ValueError('changed source, executable or environment binding')
            if result['kind'] != 'fixed' or result['function'] != f'Hex.RealClosure.Bench.{stage}':
                raise ValueError('unexpected registration')
            if result['expected_hash_check']['status'] != 'match':
                raise ValueError('expected hash check failed')
            if result['config']['repeats'] != 1 or result['config']['min_total_seconds'] != 0.2:
                raise ValueError('changed measurement configuration')
            if not result['hashes_agree'] or result['budget_truncated']:
                raise ValueError('hash disagreement or truncated result')
            points = result['points']
            if len(points) != 1:
                raise ValueError('changed repeat count')
            point = points[0]
            if point['status'] != 'ok' or point['inner_repeats'] <= 0 or point['total_nanos'] <= 0:
                raise ValueError('invalid measured point')
            if point['result_hash'] not in ('0x1', '0x0000000000000001', '1'):
                raise ValueError('changed expected functional result')
            values.append(point['total_nanos'] / point['inner_repeats'])
            batches.append({'trial': trial, 'inner_repeats': point['inner_repeats'],
                            'total_nanos': point['total_nanos']})
        summary[stage] = {'median_ms': statistics.median(values) / 1e6,
                          'minimum_ms': min(values) / 1e6, 'maximum_ms': max(values) / 1e6,
                          'per_call_nanos': values, 'batches': batches}
    return {'source': metadata['source'], 'binary_sha256': metadata['binary_sha256'],
            'cpu': metadata['cpu'], 'measurements': 24, 'stages': summary,
            'claim': 'Fixed-input inclusive stage observations; no scaling or exclusive cost claim.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    print(json.dumps(analyze(args.directory), indent=2))


if __name__ == '__main__':
    main()
