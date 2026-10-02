#!/usr/bin/env python3
"""Summarize actual transferred polynomial entries and certificate minors."""
import argparse
import gzip
import json
from pathlib import Path


def statistics(kind, entries):
    degree = support = numerator_bits = denominator_bits = 0
    for entry in entries:
        if kind == 'polymatrix':
            terms = [(i, int(a), int(b)) for i, (a, b) in enumerate(zip(entry['num'], entry['den'])) if int(a)]
        else:
            terms = [(sum(exponents), int(coefficient), 1) for exponents, coefficient in entry if int(coefficient)]
        degree = max(degree, max((term[0] for term in terms), default=0))
        support = max(support, len(terms))
        numerator_bits = max(numerator_bits, max((abs(term[1]).bit_length() for term in terms), default=0))
        denominator_bits = max(denominator_bits, max((term[2].bit_length() for term in terms), default=0))
    return dict(max_degree=degree, max_support=support,
                max_numerator_bits=numerator_bits, max_denominator_bits=denominator_bits)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    payload = gzip.decompress(args.input.read_bytes()) if args.input.suffix == '.gz' else args.input.read_bytes()
    results = []
    for line in payload.splitlines():
        request = json.loads(line)
        record, cert = request['record'], request['certificate']
        kind = record['kind']
        results.append({'carrier': 'RatPoly' if kind == 'polymatrix' else 'Mv',
            'dimension': record['rows'], 'rank': cert['rank'],
            'input': statistics(kind, [x for row in record['entries'] for x in row]),
            'denominator': statistics(kind, [cert['denom']]),
            'adjugate': statistics(kind, [x for row in cert['adj'] for x in row])})
    args.out.write_text(json.dumps(results, indent=2) + '\n')


if __name__ == '__main__':
    main()
