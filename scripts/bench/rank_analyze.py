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
    directories = directory if isinstance(directory, list) else [directory]
    groups = defaultdict(list)
    failures = []
    for source in directories:
        control = source / 'overhead.json'
        local_overhead = json.loads(control.read_text())['results'][0]['median_nanos'] if control.exists() else overhead
        for command, export in completed(source):
            if command['label'] == 'overhead':
                continue
            if export is None or command['exit_code'] or command.get('output_errors'):
                failures.append({**command, 'source_directory': str(source)})
            if export is None:
                results = [{'function': name, 'median_nanos': None, 'hashes_agree': False,
                            'expected_hash_check': {'status': 'missing'}}
                           for name in command['command'][2:4]]
            else:
                results = export['results']
            native = next(x for x in results if '.Comparison.' not in x['function'] or '.native' in x['function'])
            external = next(x for x in results if x is not native)
            block, label = command['label'].split('-', 1)
            a, b = native['median_nanos'], external['median_nanos']
            agreed = all(x['hashes_agree'] and x['expected_hash_check']['status'] == 'match' for x in results)
            ok = agreed and a is not None and b is not None and not command['exit_code'] and not command.get('output_errors')
            groups[label].append({'block': int(block), 'native_ns': a, 'external_ns': b,
                'protocol_ns': local_overhead, 'status': 'ok' if ok else 'failed',
                'raw_ratio': a / b if ok else None,
                'adjusted_ratio': a / (b - local_overhead) if ok and b > local_overhead else None,
                'all_agreed': agreed,
                'source': str(source / (command['label'] + '.json')), 'native_case': native['function'],
                'external_case': external['function']})
    curves = []
    for label, blocks in sorted(groups.items()):
        if len({x['block'] for x in blocks}) != len(blocks):
            raise ValueError('duplicate completed block for ' + label)
        paired = [x for x in blocks if x['status'] == 'ok']
        attempts_complete = {x['block'] for x in blocks} == set(range(6))
        complete = attempts_complete and len(paired) == 6
        if paired:
            a, b = median(x['native_ns'] for x in paired), median(x['external_ns'] for x in paired)
            adjusted = median(x['external_ns'] - x['protocol_ns'] for x in paired)
            fraction = max(x['protocol_ns'] / x['external_ns'] for x in paired)
        else:
            a = b = adjusted = fraction = None
        curves.append({'label': label, 'blocks': sorted(blocks, key=lambda x: x['block']),
            'attempts_complete': attempts_complete, 'complete': complete, 'successful_pairs': len(paired),
            'native_ns': a, 'external_ns': b, 'raw_ratio': a / b if paired else None,
            'paired_median_ratio': median(x['raw_ratio'] for x in paired) if paired else None,
            'adjusted_ratio': a / adjusted if paired and adjusted > 0 else None,
            'overhead_fraction': fraction, 'eligible': bool(complete and fraction <= .5 and max(a, b) <= 10e9),
            'above_soft_limit': max(a, b) > 1e9 if paired else None})

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


def verify(result):
    errors = []
    for name, expected in (('rank', 156), ('stages', 24)):
        section = result[name]
        if len(section['curves']) != expected or any(not row['attempts_complete'] for row in section['curves']):
            errors.append(name + ': incomplete declared six-block schedule')
        failed_paths = {block['source'] for row in section['curves'] for block in row['blocks'] if block['status'] != 'ok'}
        for filename in failed_paths:
            path = Path(filename)
            try:
                measurements = json.loads(path.read_text())['results']
                statuses = [point['status'] for m in measurements for point in m['points']]
                # Censored informational rungs are retained and excluded from
                # eligibility. A wrong successful output is never excused.
                censored = 'killed_at_cap' in statuses and all(s in ('ok', 'killed_at_cap') for s in statuses)
                valid_successes = all(m['hashes_agree'] and m['expected_hash_check']['status'] == 'match'
                    for m in measurements if m['median_nanos'] is not None)
                if not censored or not valid_successes:
                    errors.append('invalid comparison: ' + str(path))
            except (OSError, ValueError, KeyError, TypeError):
                errors.append('invalid comparison export: ' + str(path))
    if len(result['polynomial_budgets']) != 60 or any(row['verdict'] != 'pass' for row in result['polynomial_budgets']):
        errors.append('polynomial absolute budgets are incomplete or failing')
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--comparisons', type=Path, action='append', required=True, help='Initial directory and each disjoint resumed partition; repeat the flag.')
    parser.add_argument('--stages', type=Path, required=True)
    parser.add_argument('--polynomial', type=Path, required=True)
    parser.add_argument('--protocol', type=Path, required=True)
    parser.add_argument('--policy', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--verify', action='store_true', help='Require complete schedules, valid outputs, and all 60 polynomial budgets.')
    parser.add_argument('--curves', type=Path, help='Write the rank-ratio JSONL consumed by the plots.')
    args = parser.parse_args()
    overhead = json.loads((args.protocol / 'overhead.json').read_text())['results'][0]['median_nanos']
    ranks, stages = curve(args.comparisons, overhead), curve(args.stages, overhead)
    result = {'protocol_ns': overhead, 'rank': ranks, 'stages': stages,
              'polynomial_budgets': budgets(ranks, stages, args.polynomial, json.loads(args.policy.read_text()))}
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    if args.curves:
        args.curves.write_text(''.join(json.dumps(row) + '\n' for row in ranks['curves']))
    if args.verify:
        errors = verify(result)
        if errors:
            raise SystemExit('\n'.join(errors))
        print('rank analysis: complete schedules, valid observed outputs, 60 passing absolute budgets')


if __name__ == '__main__':
    main()
