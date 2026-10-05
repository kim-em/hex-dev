#!/usr/bin/env python3
"""Check retained raw arms and summarize the fixed nested comparison."""
import argparse
import json
from pathlib import Path
import statistics

from real_closure_nested_measurement import PARAMETERS, TRIALS, TARGET_NANOS, benchmark, digest, schedule


def summarize(folder):
    manifest = json.loads((folder / 'manifest.json').read_text())
    if (manifest['status'] != 'completed' or manifest['trials'] != TRIALS
            or manifest['parameters'] != [list(p) for p in PARAMETERS]
            or manifest['target_inner_nanos'] != TARGET_NANOS):
        raise ValueError('incomplete or different fixed schedule')
    for name, expected in manifest['artifacts'].items():
        if Path(name).name != name or digest(folder / name) != expected:
            raise ValueError('artifact changed or invalid filename: ' + name)
    attempts = manifest['measurements']
    if [(r['trial'], r['depth'], r['steps'], r['arm']) for r in attempts] != schedule():
        raise ValueError('measurement order differs from protocol')
    for attempt in attempts:
        output = attempt['output']
        if Path(output).name != output or output not in manifest['artifacts']:
            raise ValueError('measurement output is not a retained artifact')
        commands = [c for c in manifest['commands'] if c['stdout'] == output]
        if len(commands) != 1:
            raise ValueError('missing or ambiguous command binding')
        command = commands[0]
        original = [json.loads(line) for line in (folder / output).read_text().splitlines() if line.startswith('{')]
        if original != attempt['rows'] or len(original) != 1 or attempt['exit_code'] != 0 or command['exit_code'] != 0 or command['incomplete']:
            raise ValueError('measurement differs from completed raw output')
        name = benchmark(attempt['depth'], attempt['steps'], attempt['arm'])
        if command['argv'][-6:] != ['_child', '--bench', name, '--fixed', '--min-total-nanos', str(TARGET_NANOS)]:
            raise ValueError('command timing parameters changed')
        row = original[0]
        if (row['status'] != 'ok' or row['kind'] != 'fixed' or row['function'] != name
                or row['result_hash'] != manifest['expected_hashes'][f'{attempt["depth"]}:{attempt["steps"]}'][attempt['arm']]
                or row['env']['git_commit'] != manifest['commit'] or row['env']['git_dirty'] is not False
                or row['total_nanos'] < TARGET_NANOS or row['inner_repeats'] <= 0):
            raise ValueError('result, source or timing binding failed')
    summary = []
    for depth, steps in PARAMETERS:
        selected = [r for r in attempts if (r['depth'], r['steps']) == (depth, steps)]
        values = {arm: [r['rows'][0]['total_nanos'] / r['rows'][0]['inner_repeats']
                        for r in selected if r['arm'] == arm] for arm in 'AB'}
        ratios = [b / a for a, b in zip(values['A'], values['B'])]
        direction = ('eager faster throughout' if all(r < 1 for r in ratios) else
                     'clean faster throughout' if all(r > 1 for r in ratios) else 'mixed/inconclusive')
        summary.append(dict(depth=depth, steps=steps, direction=direction,
            clean_ms=statistics.median(values['A']) / 1e6, eager_ms=statistics.median(values['B']) / 1e6,
            paired_eager_over_clean_median=statistics.median(ratios),
            paired_eager_over_clean_range=[min(ratios), max(ratios)],
            clean_range_ms=[min(values['A']) / 1e6, max(values['A']) / 1e6],
            eager_range_ms=[min(values['B']) / 1e6, max(values['B']) / 1e6],
            inner_repeats={arm: [r['rows'][0]['inner_repeats'] for r in selected if r['arm'] == arm] for arm in 'AB'}))
    return dict(commit=manifest['commit'], executable_sha256=manifest['executable_sha256'],
                cpu=manifest['cpu'], complete_arms=len(attempts), trials=TRIALS, summary=summary,
                interpretation='Descriptive shared-host observations for the specified nested quadratic towers and product chains. '
                'Includes arithmetic, raw coefficient encoding and hashing; excludes context construction, evidence production and replay. '
                'No asymptotic, normalization policy, significance or absolute budget conclusion.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    folder = parser.parse_args().directory
    result = summarize(folder)
    with (folder / 'analysis.json').open('x') as out:
        json.dump(result, out, indent=2)
        out.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
