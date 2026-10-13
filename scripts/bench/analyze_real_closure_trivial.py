#!/usr/bin/env python3
"""Audit the retained rational root route comparison and paired estimates."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import statistics

import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.analyze_real_closure_samples import audit_archive

CASES = ('Zero', 'Constant', 'Multiplicity1', 'Multiplicity2', 'Multiplicity4', 'Multiplicity8')


def summarize(values):
    return dict(samples=len(values), median=statistics.median(values),
                minimum=min(values), maximum=max(values), values=values)


def analyze(directory, archive_index):
    directory = Path(directory)
    metadata = json.loads((directory / 'metadata.json').read_text())
    if metadata['status'] != 'completed' or len(metadata['observations']) != 72:
        raise ValueError('capture did not complete all 72 registered arms')
    if metadata['rounds'] != 6 or tuple(metadata['cases']) != CASES:
        raise ValueError('capture changed the registered workload')
    if metadata['affinity'] != [metadata['cpu']]:
        raise ValueError('capture affinity differs from the selected CPU')
    if not isinstance(archive_index, dict) or not all(
            name in archive_index for name in ('omitted_executable', 'source_git_blobs', 'source')):
        raise ValueError('committed archive index is required')
    omitted = archive_index['omitted_executable']
    if archive_index['source'] != metadata['source']:
        raise ValueError('archive source differs from original capture')
    for name, expected in metadata['artifacts'].items():
        path = directory / name
        if not path.is_file() and omitted and name == omitted['path'] and expected == omitted['sha256']:
            continue
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('retained artifact digest differs: ' + name)
    for name, expected in metadata['source_hashes'].items():
        if metadata['artifacts']['sources/' + name] != expected:
            raise ValueError('source snapshot differs from recorded source: ' + name)
    if set(archive_index['source_git_blobs']) != set(metadata['source_hashes']):
        raise ValueError('committed source snapshot set differs')
    for name, expected in archive_index['source_git_blobs'].items():
        data = (directory / 'sources' / name).read_bytes()
        blob = b'blob ' + str(len(data)).encode() + b'\0' + data
        if hashlib.sha1(blob).hexdigest() != expected:
            raise ValueError('source snapshot differs from committed Git blob: ' + name)
    if metadata['binary_sha256'] != omitted['sha256']:
        raise ValueError('measured executable digest differs from its archive index')
    commands = metadata['commands']
    preparation = {command['stdout']: command for command in commands[:6]}
    labels = ('compiler-version.stdout', 'build.stdout', 'lean-version.stdout',
              'cpu-info.stdout', 'functional.stdout', 'oracle.stdout')
    if set(preparation) != set(labels):
        raise ValueError('preparation command labels differ')
    for name in labels:
        if preparation[name]['exit_code'] != 0:
            raise ValueError('preparation command failed: ' + name)
    functional = preparation['functional.stdout']
    executable = functional['command'][0]
    if functional['command'][1:] != ['emit'] or Path(executable).name != omitted['path']:
        raise ValueError('functional command has a different measured executable')
    if (directory / functional['stderr']).read_bytes():
        raise ValueError('functional run reported an error or panic')
    fixture = directory / 'sources/conformance-fixtures/HexRealClosure/trivial-measurements.jsonl'
    if (directory / 'functional.stdout').read_bytes() != fixture.read_bytes():
        raise ValueError('functional output differs from the committed fixture')
    oracle = json.loads((directory / 'oracle.stdout').read_text())
    if oracle['verified_arms'] != 12 or oracle['oracle'] != 'python-flint 0.9.0 / FLINT 3.6.0':
        raise ValueError('exact oracle coverage or version differs')
    oracle_command = preparation['oracle.stdout']
    if (len(oracle_command['command']) != 3
            or Path(oracle_command['command'][1]).parts[-3:] !=
                ('scripts', 'oracle', 'real_closure_trivial_measurements.py')
            or Path(oracle_command['command'][2]) != Path(executable).parent / 'functional.stdout'):
        raise ValueError('oracle command has a different script or functional input')
    if (directory / oracle_command['stderr']).read_bytes():
        raise ValueError('oracle run reported an error')
    expected_schedule = []
    for trial in range(6):
        for case in CASES:
            arms = ('generic', 'canonical') if trial % 2 == 0 else ('canonical', 'generic')
            expected_schedule.extend((trial, case, 'generic', arm) for arm in arms)
    rows = metadata['observations']
    if [(r['trial'], r['case'], r['pair'], r['arm']) for r in rows] != expected_schedule:
        raise ValueError('paired adjacency or alternating trial schedule changed')
    timings = {}
    details = []
    for row in rows:
        export = json.loads((directory / row['export']).read_text())
        if len(export['results']) != 1 or export['export_schema_version'] != 1:
            raise ValueError('unexpected benchmark export schema')
        result = export['results'][0]
        expected = f'Hex.RealClosure.TrivialMeasurements.{row["case"]}.{row["arm"]}'
        if (result['function'] != expected or result['env']['git_commit'] != metadata['source']
                or result['env']['git_dirty']):
            raise ValueError('export changed its registered function or frozen source')
        command = metadata['commands'][row['command_index']]
        if (command['command'][:2] != [executable, 'run']
                or command['exit_code'] != row['exit_code'] or command['command'][2] != expected
                or Path(command['command'][-1]).name != row['export']):
            raise ValueError('observation differs from recorded command')
        if (directory / command['stderr']).read_bytes():
            raise ValueError('benchmark parent driver reported an error')
        if row['exit_code'] != 0 or result['budget_truncated'] or not result['hashes_agree']:
            raise ValueError('failed, truncated or inconsistent benchmark arm')
        if result['expected_hash_check']['status'] != 'match' or result['observed_hash'] != '0x1':
            raise ValueError('complete root consumer hash did not match')
        config = result['config']
        if (config['repeats'] != 1 or config['min_total_seconds'] != 0.5
                or not config['warmup_first_iter'] or config['max_seconds_per_call'] != 120):
            raise ValueError('fixed-call protocol differs from registration')
        points = result['points']
        if (len(points) != 1 or points[0]['status'] != 'ok'
                or points[0]['inner_repeats'] <= 0 or points[0]['total_nanos'] <= 0):
            raise ValueError('incomplete fixed-call batch')
        point = points[0]
        estimate = point['total_nanos'] / point['inner_repeats'] / 1e6
        timings[row['trial'], row['case'], row['arm']] = estimate
        details.append(dict(**row, per_call_ms=estimate, raw_point=point,
                            config=config, budget_truncated=result['budget_truncated']))
    comparisons = []
    for case in CASES:
        generic = [timings[trial, case, 'generic'] for trial in range(6)]
        canonical = [timings[trial, case, 'canonical'] for trial in range(6)]
        comparisons.append(dict(case=case, generic_ms=summarize(generic),
                                canonical_ms=summarize(canonical),
                                generic_over_canonical=summarize([a/b for a, b in zip(generic, canonical)]),
                                generic_minus_canonical_ms=summarize([a-b for a, b in zip(generic, canonical)])))
    return dict(source=metadata['source'], cpu=metadata['cpu'], host=metadata['host'],
                observations=72, comparisons=comparisons, raw_batches=details,
                inference='descriptive paired batch estimates on this shared host; no significance or asymptotic claim')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--archive-index', type=Path, required=True)
    args = parser.parse_args()
    index = audit_archive(args.directory, args.archive_index, 'capture_sha256')
    args.output.write_text(json.dumps(analyze(args.directory, index), indent=2) + '\n')


if __name__ == '__main__':
    main()
