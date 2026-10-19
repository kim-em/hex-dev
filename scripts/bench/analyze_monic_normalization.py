"""Validate the complete registered monic-clean fixed capture."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import statistics

STAGES = tuple(f'Depth{d}.monic{m}' for d in (1, 2) for m in (2, 4, 8, 16))


def analyze(directory: Path, fixture: Path) -> dict:
    metadata = json.loads((directory / 'metadata.json').read_text())
    if hashlib.sha256(fixture.read_bytes()).hexdigest() != metadata['functional_fixture_sha256']:
        raise ValueError('functional fixture binding changed')
    rows = [json.loads(line) for line in fixture.read_text().splitlines()]
    if [(r['depth'], r['steps']) for r in rows] != [(d, m) for d in (1, 2) for m in (2, 4, 8, 16)]:
        raise ValueError('functional family changed')
    hashes = {f"Depth{r['depth']}.monic{r['steps']}": r['hash'] for r in rows}
    if metadata['rounds'] != 6 or tuple(metadata['trial_major_order']) != STAGES:
        raise ValueError('registered schedule changed')
    expected = [(trial, stage) for trial in range(6) for stage in STAGES]
    observed = [(item['trial'], item['stage']) for item in metadata['observations']]
    if observed != expected or any(item['exit_code'] for item in metadata['observations']):
        raise ValueError('incomplete or failed capture')
    toolchain = metadata['lean_toolchain'].replace('leanprover/lean4:v', 'leanprover/lean4:', 1)
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
                    or environment['exe_name'] != 'hexrealclosure_nested_normalization'
                    or environment['hostname'] != metadata['host']
                    or environment['lean_toolchain'] != toolchain):
                raise ValueError('source, executable or environment binding changed')
            if result['kind'] != 'fixed' or result['function'] != f'Hex.RealClosure.NestedNormalization.Measure.{stage}':
                raise ValueError('unexpected registration')
            if result['expected_hash_check']['status'] != 'match' or not result['hashes_agree'] or result['budget_truncated']:
                raise ValueError('functional failure or truncated result')
            if result['config']['repeats'] != 1 or result['config']['min_total_seconds'] != 0.5:
                raise ValueError('measurement configuration changed')
            points = result['points']
            if len(points) != 1:
                raise ValueError('repeat count changed')
            point = points[0]
            if point['status'] != 'ok' or point['inner_repeats'] <= 0 or point['total_nanos'] <= 0:
                raise ValueError('invalid measured point')
            if int(point['result_hash'], 16) != hashes[stage]:
                raise ValueError('observed value differs from checked endpoint')
            values.append(point['total_nanos'] / point['inner_repeats'])
            batches.append({'trial': trial, 'inner_repeats': point['inner_repeats'],
                            'total_nanos': point['total_nanos']})
        summary[stage] = {'median_ms': statistics.median(values) / 1e6,
                          'minimum_ms': min(values) / 1e6, 'maximum_ms': max(values) / 1e6,
                          'per_call_nanos': values, 'batches': batches}
    return {'source': metadata['source'], 'binary_sha256': metadata['binary_sha256'],
            'cpu': metadata['cpu'], 'measurements': 48, 'endpoints': summary,
            'claim': 'Fixed monic-clean production observations; no scaling or cross-family policy claim.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('fixture', type=Path)
    args = parser.parse_args()
    print(json.dumps(analyze(args.directory, args.fixture), indent=2))


if __name__ == '__main__':
    main()
