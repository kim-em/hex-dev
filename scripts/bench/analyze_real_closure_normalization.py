#!/usr/bin/env python3
"""Summarize the preregistered paired normalization schedule, retaining all arms.

The median of six values is the arithmetic mean of the middle two sorted values.
No automatic or manual rerun follows an inconclusive comparison.
"""
import argparse
import hashlib
import json
import statistics
from pathlib import Path


def summarize(folder):
    manifest = json.loads((folder / 'manifest.json').read_text())
    if manifest['status'] != 'completed':
        raise ValueError('incomplete fixed schedule')
    for name, expected in manifest['artifacts'].items():
        if Path(name).name != name:
            raise ValueError('artifact name is not a flat filename')
        with (folder / name).open('rb') as source:
            actual = hashlib.file_digest(source, 'sha256').hexdigest()
        if actual != expected:
            raise ValueError('artifact changed: ' + name)
    rows = manifest['measurements']
    schedule = [(trial, degree, arm) for trial in range(6) for degree in (2, 4, 8, 16)
                for arm in ('AB' if trial % 2 == 0 else 'BA')]
    if [(r['trial'], r['degree'], r['arm']) for r in rows] != schedule:
        raise ValueError('schedule mismatch')
    for attempt in rows:
        original = [json.loads(line) for line in (folder / Path(attempt['output']).name).read_text().splitlines()
                    if line.startswith('{')]
        if original != attempt['rows'] or len(original) != 1 or attempt['exit_code'] != 0:
            raise ValueError('measurement disagrees with retained command output')
        row = original[0]
        name = 'Hex.RealClosure.Normalization.' + ('clean' if attempt['arm'] == 'A' else 'eager') + str(attempt['degree'])
        if (row['status'] != 'ok' or row['kind'] != 'fixed' or row['function'] != name or
            row['result_hash'] != manifest['expected_hashes'][str(attempt['degree'])][attempt['arm']] or
            row['env']['git_commit'] != manifest['commit'] or row['env']['git_dirty'] is not False or
            row['total_nanos'] <= 0 or row['inner_repeats'] <= 0):
            raise ValueError('measurement failed its arithmetic or source binding')
    summary = []
    for degree in (2, 4, 8, 16):
        values = {arm: [r['rows'][0]['total_nanos'] / r['rows'][0]['inner_repeats']
                       for r in rows if r['degree'] == degree and r['arm'] == arm] for arm in 'AB'}
        ratios = [b / a for a, b in zip(values['A'], values['B'])]
        direction = ('eager faster throughout' if all(r < 1 for r in ratios) else
                     'clean faster throughout' if all(r > 1 for r in ratios) else 'mixed/inconclusive')
        summary.append(dict(degree=degree, direction=direction,
            clean_ms=statistics.median(values['A']) / 1e6, eager_ms=statistics.median(values['B']) / 1e6,
            paired_eager_over_clean_median=statistics.median(ratios),
            paired_eager_over_clean_min=min(ratios), paired_eager_over_clean_max=max(ratios),
            clean_range_ms=[min(values['A']) / 1e6, max(values['A']) / 1e6],
            eager_range_ms=[min(values['B']) / 1e6, max(values['B']) / 1e6]))
    return dict(commit=manifest['commit'], executable_sha256=manifest['executable_sha256'],
        cpu=manifest['cpu'], complete_arms=len(rows), trials=6, summary=summary,
        interpretation='Descriptive shared-host data retaining all six trials. One Rat extension, 2n products, '
        'stored eager denominators at most 4; the selected root uses direct Sturm rather than BKR. '
        'Degree 2 uses the linear endpoint fast path. No policy, significance, scaling or regression-budget conclusion.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    folder = parser.parse_args().directory
    output = summarize(folder)
    with (folder / 'analysis.json').open('x') as destination:
        json.dump(output, destination, indent=2)
        destination.write('\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
