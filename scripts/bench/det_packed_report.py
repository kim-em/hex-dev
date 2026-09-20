#!/usr/bin/env python3
"""Render retained packed comparison observations without discarding losing cells."""
import argparse
from collections import Counter, defaultdict
import gzip
import json
from pathlib import Path
import re
import statistics


def median(xs):
    return statistics.median(xs) if xs else None


def fmt(ns):
    return '—' if ns is None else f'{ns / 1e6:.2f}'


def read_record(directory, name):
    path = directory / (name + '.json.gz')
    if path.exists():
        return json.loads(gzip.decompress(path.read_bytes()))
    return json.loads((directory / (name + '.json')).read_text())


def audit_dispatch(record, table):
    """Check actual routes against the fixed table, including retained records."""
    keys = {tuple(k) for k in table['keys']}
    for sample in record['samples']:
        if sample['arm'] != 'Dispatch' or sample['candidate']['state'] != 'complete':
            continue
        stem = sample['stem']
        classified = record['classification'][stem]
        if classified['classification'] not in ['eligible', 'packed-decline']:
            continue
        products = classified['selection']['products']
        packed = classified['classification'] == 'eligible' and all(tuple(p['key']) in keys for p in products)
        expected = 'packed/plain' if packed else 'term-list'
        certificates = [e for e in sample['routes'] if e['route'].startswith(('packed/', 'term-list'))]
        # Proof-node declines can follow product eligibility. They are retained as fallback,
        # but a covered witness must actually exercise the packed route to validate dispatch.
        if not packed and not certificates and any(e['route'] == 'fallback' for e in sample['routes']):
            continue
        if len(certificates) != 1 or certificates[0]['route'] != expected:
            raise ValueError(f'{stem}: expected {expected}, saw {sample["routes"]}')
        if packed:
            actual = [list(map(int, re.findall(r':= (\d+)', p['key']))) for p in certificates[0]['products']]
            if actual != [p['key'] for p in products]:
                raise ValueError(f'{stem}: dispatched witness keys differ from preflight')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    forced = read_record(args.directory, 'forced')
    dispatch = read_record(args.directory, 'dispatch')
    audit_dispatch(dispatch, read_record(args.directory, 'crossover'))
    groups = defaultdict(list)
    for c in forced['manifest']['cases']:
        groups[c['family']].append(c['stem'])
    print('Times are medians in milliseconds of six-sample, import-baseline-subtracted')
    print('fresh-module medians. Counts show cases with all six successful samples;')
    print('incomplete cases remain in the denominator and in the full ladder below.\n')
    print('| Family | Term lists | Packed | Dispatch | Mathlib | Median M/D | Complete cases L/P/D/M | Decision |')
    print('|---|---:|---:|---:|---:|---:|---|---|')
    for family, stems in groups.items():
        values, counts = [], []
        for record, arm in [(forced,'Lists'),(forced,'Packed'),(dispatch,'Dispatch'),(dispatch,'Mathlib')]:
            xs = [record['summary'][s]['arms'][arm]['median_delta_ns'] for s in stems]
            xs = [x for x in xs if x is not None]
            values.append(fmt(median(xs)))
            counts.append(str(len(xs)))
        ratios = []
        for s in stems:
            a = dispatch['summary'][s]['arms']
            d, m = a['Dispatch']['median_delta_ns'], a['Mathlib']['median_delta_ns']
            if d is not None and m is not None and d > 0 and m > 0:
                ratios.append(m / d)
        ratio = f'{median(ratios):.3f}' if ratios else '—'
        print(f'| {family} | '+ ' | '.join(values)+f' | {ratio} | {"/".join(counts)} of {len(stems)} | opt-in |')
    print('\nClassification: '+', '.join(f'{v} {k}' for k,v in Counter(c['classification'] for c in forced['classification'].values()).items())+'.')
    print(f"The manifest also retains {len(forced['manifest']['infeasible'])} infeasible support requests.\n")
    print('| Case | Classification | Term lists | Packed | Dispatch | Mathlib | Mathlib / dispatch | Observed dispatch |')
    print('|---|---|---:|---:|---:|---:|---:|---|')
    for c in forced['manifest']['cases']:
        stem = c['stem']
        vals = [r['summary'][stem]['arms'][a]['median_delta_ns'] for r,a in
                [(forced,'Lists'),(forced,'Packed'),(dispatch,'Dispatch'),(dispatch,'Mathlib')]]
        ratio = f'{vals[3]/vals[2]:.3f}' if vals[2] is not None and vals[3] is not None and vals[2]>0 else '—'
        routes = dispatch['summary'][stem]['arms']['Dispatch']['routes']
        routes = [r for r in routes if r != 'certificate-attempt']
        print(f'| {stem} | {forced["classification"][stem]["classification"]} | '+
              ' | '.join(map(fmt,vals))+f' | {ratio} | {", ".join(routes) or "unobserved"} |')
    print('\nExpected declines have no forced-packed timing. Closed-form rows are controls on')
    print('their unchanged route; their “Lists” and “Packed” column labels denote options,')
    print('not certificate execution. Raw records retain timeouts, errors, host context,')
    print('compiler output, routes, proof nodes, bounds, and artifact sizes.')

    print('\n### Crossover margins and spread\n')
    print('Median and minimum–maximum of six baseline-subtracted samples, milliseconds.')
    print('The preregistered admission rule has no effect-size floor; overlapping ranges')
    print('and very small median differences do not establish a robust speed advantage.\n')
    print('| Witness | List median | List range | Packed median | Packed range | Median reduction |')
    print('|---|---:|---|---:|---|---:|')
    for stem in read_record(args.directory, 'crossover')['winning_cases']:
        arms = [[s['delta_ns'] for s in forced['samples'] if s['stem'] == stem and s['arm'] == arm]
                for arm in ['Lists', 'Packed']]
        l, p = map(median, arms)
        print(f'| {stem} | {fmt(l)} | {fmt(min(arms[0]))}–{fmt(max(arms[0]))} | '+
              f'{fmt(p)} | {fmt(min(arms[1]))}–{fmt(max(arms[1]))} | {100 * (1-p/l):.2f}% |')

    print('\n### Representative profiles\n')
    print('One automatic-dispatch profile per family; milliseconds, with no baseline subtraction.')
    print('Kernel is the synchronous declaration check, including certificate replay and transport.')
    print('For the closed-form AlgebraicScope control it is Lean’s final type-checking time.')
    print('Identification includes the residue matrix-identification phase. Elaboration includes')
    print('the whole module. Nested phases are not additive. A dash means not applicable.\n')
    print('| Case | Conversion | Lists | Quotients | Preflight | Identification | Kernel | Elaboration |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|')
    for p in dispatch['profiles']:
        values = {name: float(value) * (1000 if unit == 's' else 1)
                  for name, value, unit in re.findall(
                      r'^\s+(det\.symbolic\.\w+|elaboration|type checking) ([0-9.e+-]+)(ms|s)$',
                      p['result'].get('compiler_output', ''), re.MULTILINE)}
        keys = ['convert', 'lists', 'quotients', 'preflight', 'identification', 'kernel']
        xs = [values.get('det.symbolic.' + k) for k in keys]
        if p['stem'] == 'AlgebraicScope':
            xs[5] = values.get('type checking')
        if xs[4] is not None:
            xs[4] += values.get('det.symbolic.matrix', 0)
        xs.append(values.get('elaboration'))
        print(f'| {p["stem"]} | '+' | '.join('—' if x is None else f'{x:.3f}' for x in xs)+' |')

    print('\n### Compiled phases\n')
    print('Milliseconds for representative witnesses, with the large-prime case included.')
    print('Checker columns are medians of six adjacent AB/BA measurements; other phases')
    print('are single observations. Packing repeats each prefix and includes target and quotient lists.')
    print('All selected products use plain multiplication, so outer signed packing is inapplicable.\n')
    print('| Case | p | Quotient support | Quotients | Preflight | Packing | Multiplication | List Bool | Packed Bool |')
    print('|---|---:|---:|---:|---:|---:|---:|---:|---:|')
    cases = {c['stem']: c for c in forced['manifest']['cases']}
    representatives = set(forced['manifest']['profiles'].values()) | {'Residue2147483647', 'Residue2147483647Missing'}
    for p in forced['profiles']:
        if p['stem'] not in representatives:
            continue
        c = p.get('compiled') or {}
        if not c:
            continue
        modulus = cases[p['stem']].get('modulus', 0)
        xs = [c.get(k) for k in ['quotient_ns', 'preflight_ns', 'packing_ns', 'multiplication_ns']]
        if not modulus or cases[p['stem']].get('missing'):
            xs[0] = None
        xs.extend(median([s['ns'] for s in c['samples'] if s['arm'] == a]) for a in ['term-list', 'packed'])
        print(f'| {p["stem"]} | {modulus or "—"} | {c["selection"]["quotient_support"]} | '+
              ' | '.join('—' if x is None else f'{x / 1e6:.4f}' for x in xs)+' |')

    print('\n### Composed Mathlib fallback\n')
    print('Full dispatched invocations that emit a fallback event, including work before delegation.')
    print('Each median requires six completed samples; incomplete cases remain visible.\n')
    print('| Case | Dispatch ms | Mathlib ms | Completed D/M |')
    print('|---|---:|---:|---|')
    stems = sorted({s['stem'] for s in dispatch['samples'] if s['arm'] == 'Dispatch'
                    and any(e['route'] == 'fallback' for e in s['routes'])})
    for stem in stems:
        a = dispatch['summary'][stem]['arms']
        print(f'| {stem} | {fmt(a["Dispatch"]["median_delta_ns"])} | {fmt(a["Mathlib"]["median_delta_ns"])} | '+
              '/'.join(str(a[k]['completed']) for k in ['Dispatch', 'Mathlib'])+' |')

if __name__ == '__main__':
    main()
