#!/usr/bin/env python3
"""Audit all retained matched sample arms and report paired batch estimates."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import statistics

GAPS = (0, 4, 8, 12)
PAIRS = ('midpoint', 'dyadic')


def summarize(values):
    return dict(samples=len(values), median=statistics.median(values),
                minimum=min(values), maximum=max(values), values=values)


def analyze(directory, archive_index=None):
    directory = Path(directory)
    metadata = json.loads((directory / 'metadata.json').read_text())
    if metadata['status'] != 'completed' or len(metadata['observations']) != 96:
        raise ValueError('capture did not complete all 96 registered arms')
    omitted = archive_index.get('omitted_executable') if archive_index else None
    if archive_index and archive_index['source'] != metadata['source']:
        raise ValueError('archive source differs from original capture')
    for name, expected in metadata['artifacts'].items():
        path = directory / name
        if not path.is_file() and omitted and name == omitted['path'] and expected == omitted['sha256']:
            continue
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('retained artifact digest differs: ' + name)
    expected_schedule = []
    for trial in range(6):
        for gap in GAPS:
            for pair in PAIRS:
                arms = (pair, 'infinitesimal')
                if trial % 2:
                    arms = tuple(reversed(arms))
                expected_schedule.extend((trial, gap, pair, arm) for arm in arms)
    rows = metadata['observations']
    if [(r['trial'], r['gap'], r['pair'], r['arm']) for r in rows] != expected_schedule:
        raise ValueError('paired adjacency or alternating trial schedule changed')
    timings = {}
    details = []
    for row in rows:
        export = json.loads((directory / row['export']).read_text())
        if len(export['results']) != 1 or export['export_schema_version'] != 1:
            raise ValueError('unexpected benchmark export schema')
        result = export['results'][0]
        expected = f'Hex.RealClosure.SampleMeasurements.Gap{row["gap"]}.{row["arm"]}'
        if result['function'] != expected or result['env']['git_commit'] != metadata['source']:
            raise ValueError('export changed its registered function or source')
        if row['exit_code'] != 0 or result['budget_truncated'] or not result['hashes_agree']:
            raise ValueError('failed, truncated or inconsistent benchmark arm')
        if result['expected_hash_check']['status'] != 'match' or result['observed_hash'] != '0x1':
            raise ValueError('sample consumer hash did not match')
        points = result['points']
        if len(points) != 1 or points[0]['status'] != 'ok' or points[0]['inner_repeats'] <= 0:
            raise ValueError('incomplete fixed-call batch')
        point = points[0]
        estimate = point['total_nanos'] / point['inner_repeats'] / 1e6
        timings[row['trial'], row['gap'], row['pair'], row['arm']] = estimate
        details.append(dict(**row, per_call_ms=estimate, raw_point=point,
                            config=result['config'], budget_truncated=result['budget_truncated']))
    comparisons = []
    for gap in GAPS:
        for pair in PAIRS:
            a = [timings[trial, gap, pair, pair] for trial in range(6)]
            b = [timings[trial, gap, pair, 'infinitesimal'] for trial in range(6)]
            comparisons.append(dict(gap=gap, pair=pair, alternative_ms=summarize(a),
                                    infinitesimal_ms=summarize(b),
                                    alternative_over_infinitesimal=summarize([x/y for x, y in zip(a, b)])))
    return dict(source=metadata['source'], cpu=metadata['cpu'], host=metadata['host'],
                observations=96, comparisons=comparisons, raw_batches=details,
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
