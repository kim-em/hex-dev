#!/usr/bin/env python3
"""Summarize retained HexRank exports without rerunning or rejecting samples.

Only commands in the completion journal are read. Comparator curves retain
partial blocks but cannot claim completion until all six paired blocks exist.
Absolute polynomial budgets follow the independently committed policy.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
from statistics import median


def completed(directory):
    journal = (directory / 'commands.jsonl').read_bytes()
    journal = journal[:journal.rfind(b'\n') + 1]
    for line in journal.splitlines():
        row = json.loads(line)
        path = directory / (row['label'] + '.json')
        if not path.exists():
            yield row, None
        else:
            try:
                yield row, json.loads(path.read_text())
            except (ValueError, OSError):
                yield row, None


def curve(directory, overhead):
    groups = defaultdict(list)
    failures = []
    for command, export in completed(directory):
        if export is None or command['exit_code'] or command.get('output_errors'):
            failures.append(command)
            continue
        results = export['results']
        native = next(x for x in results if '.Comparison.' not in x['function'] or '.native' in x['function'])
        external = next(x for x in results if x is not native)
        block, label = command['label'].split('-', 1)
        a, b = native['median_nanos'], external['median_nanos']
        groups[label].append({'block': int(block), 'native_ns': a, 'external_ns': b,
            'raw_ratio': a / b, 'adjusted_ratio': a / (b - overhead) if b > overhead else None,
            'all_agreed': all(x['hashes_agree'] and x['expected_hash_check']['status'] == 'match'
                              for x in results),
            'source': command['label'] + '.json', 'native_case': native['function'],
            'external_case': external['function']})
    curves = []
    for label, blocks in sorted(groups.items()):
        a, b = median(x['native_ns'] for x in blocks), median(x['external_ns'] for x in blocks)
        curves.append({'label': label, 'blocks': blocks, 'complete': {x['block'] for x in blocks} == set(range(6)),
            'native_ns': a, 'external_ns': b, 'raw_ratio': a / b,
            'paired_median_ratio': median(x['raw_ratio'] for x in blocks),
            'adjusted_ratio': a / (b - overhead) if b > overhead else None,
            'overhead_fraction': overhead / b, 'eligible': overhead <= b / 2 and max(a, b) <= 10e9,
            'above_soft_limit': max(a, b) > 1e9})
    return {'curves': curves, 'failed_commands': failures}


def budgets(rank_curves, stage_curves, native_directory, policy):
    references = {}
    for row in rank_curves['curves'] + stage_curves['curves']:
        name = row['blocks'][0]['external_case']
        match = re.fullmatch(r'Hex.RankBench.Comparison.(RatPoly|Mv).(Full|Deficient).(external|second|check)(4|8|12)', name)
        if match:
            carrier, rank, op, size = match.groups()
            references[(carrier, rank, 'rank' if op == 'external' else op, int(size))] = row
    results = []
    for command, export in completed(native_directory):
        if export is None:
            continue
        measurement = export['results'][0]
        match = re.fullmatch(r'Hex.RankBench.run(RatPoly|Mv)(Deficient)?(Rank|Second|Check|Cert|Certify)(4|8|12)', measurement['function'])
        if not match:
            raise ValueError('unrecognized polynomial case: ' + measurement['function'])
        carrier, rank, op, size = match.groups()
        refs = [references.get((carrier, rank or 'Full', stage, int(size)))
                for stage in policy['operation_reference'][op]]
        complete = all(r is not None and r['complete'] for r in refs)
        ceiling = policy['margin'] * sum(r['external_ns'] for r in refs) if complete else None
        time = measurement['median_nanos']
        result_ok = (not command['exit_code'] and not command.get('output_errors') and
            measurement['hashes_agree'] and measurement['expected_hash_check']['status'] == 'match')
        results.append({'case': measurement['function'], 'native_ns': time, 'budget_ns': ceiling,
            'verdict': ('pass' if result_ok and time <= ceiling else 'fail') if complete else 'pending references',
            'hash_agreement': result_ok, 'source': command['label'] + '.json',
            'references': [r['label'] if r else None for r in refs]})
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--comparisons', type=Path, required=True)
    parser.add_argument('--stages', type=Path, required=True)
    parser.add_argument('--polynomial', type=Path, required=True)
    parser.add_argument('--protocol', type=Path, required=True)
    parser.add_argument('--policy', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--curves', type=Path, help='Write the rank-ratio JSONL consumed by the plots.')
    args = parser.parse_args()
    overhead = json.loads((args.protocol / 'overhead.json').read_text())['results'][0]['median_nanos']
    ranks, stages = curve(args.comparisons, overhead), curve(args.stages, overhead)
    result = {'protocol_ns': overhead, 'rank': ranks, 'stages': stages,
              'polynomial_budgets': budgets(ranks, stages, args.polynomial, json.loads(args.policy.read_text()))}
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    if args.curves:
        args.curves.write_text(''.join(json.dumps(row) + '\n' for row in ranks['curves']))


if __name__ == '__main__':
    main()
