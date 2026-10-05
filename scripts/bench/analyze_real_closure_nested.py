#!/usr/bin/env python3
"""Check retained raw arms and summarize the fixed nested comparison."""
import argparse
import json
import hashlib
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parents[2]


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def summarize(folder, *, protocol=None, identities=None, omitted_snapshot=None):
    # New captures use the current protocol. Historical archives supply their
    # versioned schedule and wording; frozen source copies are hash-checked.
    if protocol is None:
        import real_closure_nested_measurement as protocol
    PARAMETERS, TRIALS, TARGET_NANOS = protocol.PARAMETERS, protocol.TRIALS, protocol.TARGET_NANOS
    benchmark, schedule = protocol.benchmark, protocol.schedule
    manifest = json.loads((folder / 'manifest.json').read_text())
    if (manifest['status'] != 'completed' or manifest['trials'] != TRIALS
            or manifest['parameters'] != [list(p) for p in PARAMETERS]
            or manifest['target_inner_nanos'] != TARGET_NANOS):
        raise ValueError('incomplete or different fixed schedule')
    for name, expected in manifest['artifacts'].items():
        if Path(name).name != name:
            raise ValueError('artifact changed or invalid filename: ' + name)
        if omitted_snapshot is not None and name == omitted_snapshot['filename']:
            if expected != omitted_snapshot['sha256'] or (folder / name).exists():
                raise ValueError('omitted snapshot binding failed')
            continue
        if not (folder / name).is_file() or digest(folder / name) != expected:
            raise ValueError('artifact changed or invalid filename: ' + name)
    for command in manifest['commands']:
        record = Path(command['stdout']).with_suffix('.command.json').name
        if record not in manifest['artifacts'] or json.loads((folder / record).read_text()) != command:
            raise ValueError('manifest command differs from retained command record')
    if identities is None:
        identities = {'analyzer_sha256': Path(__file__),
                  'capture_script_sha256': ROOT / 'scripts/bench/real_closure_nested_measurement.py',
                  'protocol_sha256': ROOT / 'reports/bench-results/real-closure-nested-protocol.md',
                  'oracle_sha256': ROOT / 'scripts/oracle/real_closure_nested_normalization.py'}
    for key, source in identities.items():
        if digest(source) != manifest[key]:
            raise ValueError('source content key differs: ' + key)
    binary = 'hexrealclosure_nested_normalization'
    if (manifest['artifacts'].get(binary) != manifest['executable_sha256']
            or Path(manifest['snapshot_argv0']).name != binary):
        raise ValueError('snapshot executable binding failed')

    def command_for(output):
        if Path(output).name != output or output not in manifest['artifacts']:
            raise ValueError('command output is not a retained artifact')
        matches = [c for c in manifest['commands'] if c['stdout'] == output]
        if len(matches) != 1 or matches[0]['exit_code'] != 0 or matches[0]['incomplete']:
            raise ValueError('missing, ambiguous or failed completed command')
        return matches[0]

    checks = manifest['functional_checks']
    if [(c['depth'], c['steps']) for c in checks] != PARAMETERS:
        raise ValueError('functional parameter inventory differs')
    hashes = {}
    for check in checks:
        depth, steps = check['depth'], check['steps']
        hashes[f'{depth}:{steps}'] = {}
        for arm in 'AB':
            output = check['outputs'][arm]
            command = command_for(output)
            policy = 'clean' if arm == 'A' else 'eager'
            if command['argv'] != [manifest['snapshot_argv0'], str(depth), str(steps), policy, 'plain']:
                raise ValueError('functional command used another snapshot or parameter')
            original = [json.loads(line) for line in (folder / output).read_text().splitlines() if line.startswith('{')]
            if len(original) != 1:
                raise ValueError('functional endpoint row count differs')
            row = original[0]
            if ((row['depth'], row['steps'], row['eager']) != (depth, steps, arm == 'B')
                    or any(row.get(flag) is not True for flag in ('value_roundtrip', 'roots_replayed', 'query_replayed'))):
                raise ValueError('functional parameter or native replay failed')
            hashes[f'{depth}:{steps}'][arm] = f'0x{row["hash"]:x}'
        command = command_for(check['oracle_output'])
        if (Path(manifest['oracle_argv1']).name != 'real_closure_nested_normalization.py'
                or command['argv'] != [manifest['oracle_python'], manifest['oracle_argv1']]
                    + [str(Path(manifest['snapshot_argv0']).parent / check['outputs'][arm]) for arm in 'AB']):
            raise ValueError('exact oracle command is not bound to the functional pair')
        oracle = json.loads((folder / check['oracle_output']).read_text())
        if oracle['oracle'] != 'python-flint' or oracle['version'] != '0.9.0' or len(oracle['results']) != 2:
            raise ValueError('exact oracle result failed')
        if any((r['depth'], r['steps'], r['eager'], r['exact_value_checked']) != (depth, steps, arm == 'B', True)
               for r, arm in zip(oracle['results'], 'AB')):
            raise ValueError('exact oracle result names another pair')
        if oracle['results'][0]['field_residue'] != oracle['results'][1]['field_residue']:
            raise ValueError('exact semantic values differ between arms')
    if hashes != manifest['expected_hashes']:
        raise ValueError('expected hashes differ from retained functional endpoints')
    if command_for(manifest['verify_output'])['argv'] != [manifest['snapshot_argv0'], 'verify']:
        raise ValueError('verify command used another snapshot')
    attempts = manifest['measurements']
    if [(r['trial'], r['depth'], r['steps'], r['arm']) for r in attempts] != schedule():
        raise ValueError('measurement order differs from protocol')
    for attempt in attempts:
        output = attempt['output']
        if Path(output).name != output or output not in manifest['artifacts']:
            raise ValueError('measurement output is not a retained artifact')
        command = command_for(output)
        original = [json.loads(line) for line in (folder / output).read_text().splitlines() if line.startswith('{')]
        if original != attempt['rows'] or len(original) != 1 or attempt['exit_code'] != 0 or command['exit_code'] != 0 or command['incomplete']:
            raise ValueError('measurement differs from completed raw output')
        name = benchmark(attempt['depth'], attempt['steps'], attempt['arm'])
        if command['argv'] != [manifest['snapshot_argv0'], '_child', '--bench', name, '--fixed', '--min-total-nanos', str(TARGET_NANOS)]:
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
        direction = ('eager lower in all six trials' if all(r < 1 for r in ratios) else
                     'clean lower in all six trials' if all(r > 1 for r in ratios) else 'mixed/inconclusive')
        summary.append(dict(depth=depth, steps=steps, direction=direction,
            clean_ms=statistics.median(values['A']) / 1e6, eager_ms=statistics.median(values['B']) / 1e6,
            paired_eager_over_clean_median=statistics.median(ratios),
            paired_eager_over_clean_range=[min(ratios), max(ratios)],
            clean_range_ms=[min(values['A']) / 1e6, max(values['A']) / 1e6],
            eager_range_ms=[min(values['B']) / 1e6, max(values['B']) / 1e6],
            inner_repeats={arm: [r['rows'][0]['inner_repeats'] for r in selected if r['arm'] == arm] for arm in 'AB'}))
    return dict(commit=manifest['commit'], executable_sha256=manifest['executable_sha256'],
                cpu=manifest['cpu'], complete_arms=len(attempts), trials=TRIALS, summary=summary,
                interpretation=getattr(protocol, 'INTERPRETATION', 'Descriptive shared-host observations for the specified nested quadratic towers and product chains. '
                'Production clean packing leaves nonmonic-head representatives unreduced; the bench-local eager arm reduces modulo the monic cubic head with its extraneous root. '
                'Both include per-operation selected-root zero/sign queries, recursive coefficient arithmetic, raw encoding and hashing; exclude context construction, final evidence production and replay. '
                'No asymptotic, normalization policy, significance or absolute budget conclusion.'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--archive', action='store_true', help='validate the committed archive without writing or restoring its executable')
    args = parser.parse_args()
    folder = args.directory
    if args.archive:
        from check_real_closure_nested_archive import check_archive
        result = check_archive(folder)
        print(f'Archive validated: {result["complete_arms"]} arms, {len(result["summary"])} pairs, both published tables.')
        return
    result = summarize(folder)
    with (folder / 'analysis.json').open('x') as out:
        json.dump(result, out, indent=2)
        out.write('\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
