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


def selected(record):
    if record['stage'] != 'forced' or not record['schedule_complete'] or not record['sources_unchanged'] or record['subset']:
        raise ValueError('requires a complete, unchanged, full forced comparison')
    winners, keys = [], set()
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
            winners.append(stem)
            keys.update(tuple(r['key']) for r in c['selection']['products'])
    return winners, sorted(keys)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('forced', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    raw = args.forced.read_bytes()
    record = json.loads(gzip.decompress(raw) if args.forced.suffix == '.gz' else raw)
    winners, keys = selected(record)
    result = dict(forced_sha256=hashlib.sha256(args.forced.read_bytes()).hexdigest(),
        rule='six completed samples in both arms; 0 < packed median < term-list median',
        winning_cases=winners, keys=keys, default_simproc_enabled=False)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    if args.write:
        path = ROOT / 'HexPolyDet/Select.lean'
        text = path.read_text()
        table = '[\n' + ',\n'.join('  ⟨' + ', '.join(map(str,k)) + '⟩' for k in keys) + '\n]' if keys else '[]'
        text, count = re.subn(r'def crossover : List Key := \[[\s\S]*?\]', 'def crossover : List Key := '+table, text, count=1)
        if count != 1:
            raise ValueError('crossover declaration not found')
        path.write_text(text)
    print(f'{len(winners)} winning witnesses; {len(keys)} product keys')

if __name__ == '__main__':
    main()
