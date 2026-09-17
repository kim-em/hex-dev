#!/usr/bin/env python3
"""Render retained packed comparison observations without discarding losing cells."""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import statistics


def median(xs):
    return statistics.median(xs) if xs else None


def fmt(ns):
    return '—' if ns is None else f'{ns / 1e6:.2f}'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    forced = json.loads((args.directory / 'forced.json').read_text())
    dispatch = json.loads((args.directory / 'dispatch.json').read_text())
    groups = defaultdict(list)
    for c in forced['manifest']['cases']:
        groups[c['family']].append(c['stem'])
    print('Times are medians in milliseconds of six-sample, import-baseline-subtracted')
    print('fresh-module medians. Counts show cases with all six successful samples;')
    print('incomplete cases remain in the denominator and in the full ladder below.\n')
    print('| Family | Term lists | Packed | Dispatch | Mathlib | Complete cases L/P/D/M | Decision |')
    print('|---|---:|---:|---:|---:|---|---|')
    for family, stems in groups.items():
        values, counts = [], []
        for record, arm in [(forced,'Lists'),(forced,'Packed'),(dispatch,'Dispatch'),(dispatch,'Mathlib')]:
            xs = [record['summary'][s]['arms'][arm]['median_delta_ns'] for s in stems]
            xs = [x for x in xs if x is not None]
            values.append(fmt(median(xs)))
            counts.append(str(len(xs)))
        print(f'| {family} | '+ ' | '.join(values)+f' | {"/".join(counts)} of {len(stems)} | opt-in |')
    print('\nClassification: '+', '.join(f'{v} {k}' for k,v in Counter(c['classification'] for c in forced['classification'].values()).items())+'.')
    print(f"The manifest also retains {len(forced['manifest']['infeasible'])} infeasible support requests.\n")
    print('| Case | Classification | Term lists | Packed | Dispatch | Mathlib | Mathlib / dispatch |')
    print('|---|---|---:|---:|---:|---:|---:|')
    for c in forced['manifest']['cases']:
        stem = c['stem']
        vals = [r['summary'][stem]['arms'][a]['median_delta_ns'] for r,a in
                [(forced,'Lists'),(forced,'Packed'),(dispatch,'Dispatch'),(dispatch,'Mathlib')]]
        ratio = f'{vals[3]/vals[2]:.3f}' if vals[2] is not None and vals[3] is not None and vals[2]>0 else '—'
        print(f'| {stem} | {forced["classification"][stem]["classification"]} | '+
              ' | '.join(map(fmt,vals))+f' | {ratio} |')
    print('\nExpected declines have no forced-packed timing. Closed-form rows are controls on')
    print('their unchanged route; their “Lists” and “Packed” column labels denote options,')
    print('not certificate execution. Raw records retain timeouts, errors, host context,')
    print('compiler output, routes, proof nodes, bounds, and artifact sizes.')

if __name__ == '__main__':
    main()
