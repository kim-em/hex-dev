#!/usr/bin/env python3
"""Audit the retained rational root route comparison and paired estimates."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import statistics

CASES = ('Zero', 'Constant', 'Multiplicity1', 'Multiplicity2', 'Multiplicity4', 'Multiplicity8')


def summarize(values):
    return dict(samples=len(values), median=statistics.median(values),
                minimum=min(values), maximum=max(values), values=values)


def analyze(directory, archive_index=None):
    directory = Path(directory)
    metadata = json.loads((directory / 'metadata.json').read_text())
    if metadata['status'] != 'completed' or len(metadata['observations']) != 72:
        raise ValueError('capture did not complete all 72 registered arms')
    if metadata['rounds'] != 6 or tuple(metadata['cases']) != CASES:
        raise ValueError('capture changed the registered workload')
    omitted = archive_index.get('omitted_executable') if archive_index else None
    if archive_index and archive_index['source'] != metadata['source']:
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
        if (command['exit_code'] != row['exit_code'] or command['command'][2] != expected
                or Path(command['command'][-1]).name != row['export']):
            raise ValueError('observation differs from recorded command')
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
                                generic_over_canonical=summarize([a/b for a, b in zip(generic, canonical)])))
    return dict(source=metadata['source'], cpu=metadata['cpu'], host=metadata['host'],
                observations=72, comparisons=comparisons, raw_batches=details,
                inference='descriptive paired batch estimates on this shared host; no significance or asymptotic claim')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--archive-index', type=Path)
    args = parser.parse_args()
    index = json.loads(args.archive_index.read_text()) if args.archive_index else None
    args.output.write_text(json.dumps(analyze(args.directory, index), indent=2) + '\n')


if __name__ == '__main__':
    main()
