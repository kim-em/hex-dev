#!/usr/bin/env python3
"""Fix the exact packed keys from the completed forced-arm comparison.

Preregistered decision: admit the union of product keys from eligible cases
with six successful adjacent samples in each arm and a positive packed median
strictly smaller than the term-list median. All other cases contribute no keys.
This selects a checker within the opt-in handler; it does not enable a default
simproc family. Dispatch is measured only after this table is fixed.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]


def selected_tables(record):
    if record['stage'] != 'forced' or not record['schedule_complete'] or not record['sources_unchanged'] or record['subset']:
        raise ValueError('requires a complete, unchanged, full forced comparison')
    winners, tables = [], {"list": set(), "tree": set()}
    for stem, case in record['summary'].items():
        c = record['classification'][stem]
        if c['classification'] != 'eligible':
            continue
        lists = case['arms']['Lists']['median_delta_ns']
        packed = case['arms']['Packed']['median_delta_ns']
        if lists is not None and packed is not None and 0 < packed < lists:
            for arm, route in [('Lists', 'term-list'), ('Packed', 'packed/plain')]:
                samples = [r for r in record['samples'] if r['stem'] == stem and r['arm'] == arm]
                if len(samples) != 6 or not all(any(e['route'] == route for e in r.get('routes', [])) for r in samples):
                    raise ValueError(f'{stem}: six actual {route} certificates required')
            entries = c.get('entries', 'list')
            for sample in record['samples']:
                if sample['stem'] == stem and sample['arm'] == 'Packed':
                    actual = next(e for e in sample['routes'] if e['route'] == 'packed/plain')
                    if actual.get('entries', 'list') != entries:
                        raise ValueError(f'{stem}: entry encoding differs from classification')
            winners.append(stem)
            tables[entries].update(tuple(r['key']) for r in c['selection']['products'])
    return winners, {encoding: sorted(keys) for encoding, keys in tables.items()}


def selected(record):
    winners, tables = selected_tables(record)
    return winners, sorted(set(tables['list']) | set(tables['tree']))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('forced', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    raw = args.forced.read_bytes()
    record = json.loads(gzip.decompress(raw) if args.forced.suffix == '.gz' else raw)
    winners, tables = selected_tables(record)
    keys = sorted(set(tables["list"]) | set(tables["tree"]))
    result = dict(forced_sha256=hashlib.sha256(args.forced.read_bytes()).hexdigest(),
        rule='six completed samples in both arms; 0 < packed median < term-list median',
        winning_cases=winners, keys=keys, keys_by_entries=tables, default_simproc_enabled=False)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    if args.write:
        path = ROOT / 'HexPolyDet/Select.lean'
        text = path.read_text()
        for encoding, declaration in [('list', 'crossover'), ('tree', 'treeCrossover')]:
            entries = tables[encoding]
            table = '[\n' + ',\n'.join('  ⟨' + ', '.join(map(str,k)) + '⟩' for k in entries) + '\n]' if entries else '[]'
            text, count = re.subn(r'def ' + declaration + r' : List Key := \[[\s\S]*?\]',
                lambda _: 'def ' + declaration + ' : List Key := ' + table, text, count=1)
            if count != 1:
                raise ValueError(f'{declaration} declaration not found')
        path.write_text(text)
    print(f'{len(winners)} winning witnesses; {len(keys)} product keys')

if __name__ == '__main__':
    main()
