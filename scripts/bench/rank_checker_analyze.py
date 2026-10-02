#!/usr/bin/env python3
"""Validate and summarize the retained quotient checker investigation.

No fitted model or replacement verdict: the scientific results are
reported exactly as LeanBench emitted them. The two paired schedules diagnose
constants at one dimension and cannot establish a complexity pass.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics

PREFIX = 'Hex.RankBench.Quotient.'
CASES = ('checkFull', 'finishFull', 'produceFull', 'checkDeficient',
         'finishDeficient', 'produceDeficient')
SELECTORS = ('blockFull', 'blockDeficient', 'pivotColsFull', 'pivotColsDeficient')
SIZES = [128, 192, 256, 384, 512, 768, 1024]
DOT_SIZES = [1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384]


def read(path):
    return json.loads(path.read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def journal(directory, labels):
    retained = read(directory / 'retention.json')
    require(retained['completed_commands'] == labels, f'{directory}: retention schedule mismatch')
    required = {'metadata.json', 'commands.jsonl', *(label + '.json' for label in labels)}
    require(required <= retained['sha256'].keys(), f'{directory}: missing retained raw files')
    for name, expected in retained['sha256'].items():
        require(hashlib.sha256((directory / name).read_bytes()).hexdigest() == expected,
                f'{directory}: retained file hash mismatch: {name}')
    completion = read(directory / 'completion.json')
    require(completion['scheduled'] == completion['completed'] == len(labels),
            f'{directory}: incomplete schedule')
    rows = [json.loads(line) for line in (directory / 'commands.jsonl').read_text().splitlines()]
    require([row['label'] for row in rows] == labels, f'{directory}: schedule order mismatch')
    require(not completion['failures'], f'{directory}: failed commands')
    for row in rows:
        require(row['exit_code'] == 0 and not row['output_errors'],
                f'{directory}: failed output validation')
    metadata = read(directory / 'metadata.json')
    require(metadata['schedule'] == [[r['label'], r['command']] for r in rows],
            f'{directory}: journal differs from committed schedule')
    return metadata


def measurement(directory, label, case, sizes, trials):
    records = read(directory / (label + '.json'))['results']
    require(len(records) == 1, f'{directory}/{label}: unexpected result count')
    result = records[0]
    require(result['function'] == PREFIX + case and result['kind'] == 'parametric',
            f'{directory}/{label}: wrong operation')
    require(not result['budget_truncated'], f'{directory}/{label}: truncated run')
    config = result['config']
    expected_config = {'outer_trials': trials, 'target_inner_nanos': 2000000000,
                       'slope_tolerance': 0.15, 'signal_floor_multiplier': 10,
                       'verdict_warmup_fraction': 0 if trials == 1 else 0.2,
                       'param_floor': sizes[0], 'param_ceiling': sizes[-1],
                       'cache_mode': 'warm',
                       'param_schedule': 'doubling' if trials == 1 else
                           {'kind': 'custom', 'params': sizes}}
    require(all(config[k] == v for k, v in expected_config.items()),
            f'{directory}/{label}: declared protocol changed')
    points = result['points']
    require([(p['trial_index'], p['param']) for p in points] ==
            [(trial, size) for trial in range(trials) for size in sizes],
            f'{directory}/{label}: missing, duplicated or reordered sample')
    hashes = {}
    for p in points:
        # Selector values are validated structurally in Lean preparation.
        # Preserve and check their complete output hashes at every rung.
        expected = hashes.get(p['param'], p['result_hash']) if case in SELECTORS else (
            '0xb' if case.startswith(('dot', 'check')) else hex(
                p['param'] // 2 if case.endswith('Deficient') else p['param']))
        require(p['status'] == 'ok' and p['result_hash'] == expected and
                isinstance(expected, str) and expected.startswith('0x') and
                math.isfinite(p['per_call_nanos']) and p['per_call_nanos'] > 0,
                f'{directory}/{label}: invalid sample')
        hashes[p['param']] = p['result_hash']
    return result


def pairs(root, name, arms, cases, binaries):
    directory = root / name
    labels = [f'{block}-{arm}' for block in range(6)
              for arm in (arms if block % 2 == 0 else arms[::-1])]
    metadata = journal(directory, labels)
    expected = {arm: read(root / 'binaries' / (binary + '.json'))['binary_sha256']
                for arm, binary in zip(arms, binaries)}
    for label, command in metadata['schedule']:
        arm = label.split('-', 1)[1]
        require(metadata['binary_sha256'][command[0]] == expected[arm],
                f'{directory}: wrong frozen executable for {arm}')
    rows = []
    for block in range(6):
        times = [measurement(directory, f'{block}-{arm}', case, [1024], 1)
                 ['points'][0]['per_call_nanos'] / 1e9 for arm, case in zip(arms, cases)]
        rows.append({'block': block, arms[0] + '_seconds': times[0],
                     arms[1] + '_seconds': times[1], 'second_over_first': times[1] / times[0]})
    return {'directory': str(directory), 'arms': arms, 'pairs': rows,
            'median_paired_second_over_first': statistics.median(r['second_over_first'] for r in rows)}


def analyze(root, variant='borrow'):
    results = []
    cases = SELECTORS if variant == 'selection' else (*CASES, 'dot' if variant == 'borrow' else 'dotArray')
    for case in cases:
        directory = root / (variant + '-' + case)
        metadata = journal(directory, [case])
        binary = read(root / 'binaries' / (variant + '.json'))
        require(metadata['binary_sha256'] == binary['binary_sha256'] and
                all(metadata['source_sha256'].get(k) == v for k, v in binary['source_sha256'].items()),
                f'{directory}: frozen executable/source provenance mismatch')
        sizes = DOT_SIZES if case.startswith('dot') else SIZES
        result = measurement(directory, case, case, sizes, 6)
        require(result['complexity_formula'] == ('n' if case.startswith('dot') else 'n * n * n'),
                f'{case}: model changed')
        results.append({'case': PREFIX + case, 'raw': str(directory / (case + '.json')),
                        'verdict': result['verdict'], 'slope': result['slope'],
                        'samples': len(result['points']), 'sizes': sizes,
                        'largest_rung_median_seconds': statistics.median(
                            p['per_call_nanos'] / 1e9 for p in result['points'] if p['param'] == sizes[-1]),
                        'trial_summaries': result['trial_summaries']})
    summary = {'scientific': results,
            'all_scientific_consistent': all(r['verdict'] == 'consistent_with_declared_complexity'
                                            for r in results)}
    if variant == 'selection':
        return summary
    medians = {r['case'].removeprefix(PREFIX): r['largest_rung_median_seconds'] for r in results}
    summary['largest_rung_check_over_produce'] = {
        rank: medians['check' + rank] / medians['produce' + rank] for rank in ('Full', 'Deficient')}
    return {**summary,
            'context': pairs(root, 'context' if variant == 'borrow' else 'array-context',
                             ['check', 'finish'], ['checkFull', 'finishFull'],
                             ['before', 'before'] if variant == 'borrow' else ['array', 'array']),
            'implementation': pairs(root, variant + '-pairs', ['before', 'after'],
                                    ['checkFull', 'checkFull'], ['before', variant])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--variant', choices=('borrow', 'array', 'selection'), default='borrow')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--require-consistent', action='store_true',
                        help='Fail if any scientific verdict is not consistent (final Phase-4 evidence only).')
    args = parser.parse_args()
    result = analyze(args.root, args.variant)
    encoded = json.dumps(result, indent=2) + '\n'
    if args.check:
        require(args.out.read_text() == encoded, 'checker analysis does not match retained records')
    else:
        args.out.write_text(encoded)
    if args.require_consistent:
        require(result['all_scientific_consistent'], 'a scientific verdict is not consistent')
    print('complete schedules and valid outputs; all scientific consistent:',
          result['all_scientific_consistent'])


if __name__ == '__main__':
    main()
