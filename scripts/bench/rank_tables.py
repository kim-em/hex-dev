#!/usr/bin/env python3
"""Render all HexRank verdict and ratio rows from retained exports."""
import argparse
import json
from pathlib import Path
from statistics import median

RESOLUTIONS = {
    'runCheckRankLowRank2At1024': 'checker-resolution',
    'CertifyLowRank2At1024': 'certify-resolution',
    'WitnessLowRank2At1024': 'witness-resolution',
    'runRankCertDeficientHalfShifted': 'shifted-resolution',
    'SecondDeficientMinusOne': 'second-resolution',
    'CertifyDeficientHalf': 'half-certify-resolution',
}


def emit(path, text, check):
    if check:
        if not path.exists() or path.read_text() != text:
            raise SystemExit('stale rank table: ' + str(path))
    else:
        path.write_text(text)


def measurements(directory):
    for line in (directory / 'commands.jsonl').read_text().splitlines():
        command = json.loads(line)
        path = directory / (command['label'] + '.json')
        if path.exists():
            yield command['label'], path, json.loads(path.read_text())['results'][0]


def performance(row, mode):
    verdict = row['verdict']
    if verdict == 'consistent_with_declared_complexity':
        return 'consistent' if mode == 1 else 'within upper bound (observed matching)'
    if mode == 2 and row['slope'] is not None and row['slope'] < 0:
        return 'within upper bound (observed faster)'
    return 'inconclusive'


def parametric(root, directories, output, quotient=False, check=False):
    rows = []
    for directory in directories:
        if not (root / directory / 'commands.jsonl').exists():
            continue
        for label, path, row in measurements(root / directory):
            if label in RESOLUTIONS:
                replacement = root / RESOLUTIONS[label] / path.name
                if replacement.exists():
                    path = replacement
                    row = json.loads(path.read_text())['results'][0]
            name = row['function'].removeprefix('Hex.RankBench.')
            low = 'lowrank' in name.lower()
            mode = 1 if low or quotient else 2
            model = 'n * n * n' if quotient else ('1' if name.startswith('Second.') and low else
                'n * n' if low else 'hadamardBound n' if 'dense' in name.lower() else 'productBound n')
            beta = f"{row['slope']:+.3f}" if row['slope'] is not None else '—'
            eligible = len({point['param'] for point in row['points']
                if point['status'] == 'ok' and not point['below_signal_floor'] and point['part_of_verdict']})
            rows.append(f"| [`{name}`]({path.relative_to(root)}) | {mode} | `{model}` | {beta} | {eligible} | {performance(row, mode)} |")
    intro = ('# Quotient witness verdicts\n\n' if quotient else '# Integer verdicts\n\n')
    intro += ('All cases use mode 1: both directions gate. The initial 4–64 ladder and both full-checker observations are retained separately.\n\n' if quotient else 'The linked exports retain every point. Mode-2 faster results translate the harness’s `inconclusive` result using the declared one-sided bound; they are not two-sided passes. The original resolution failures remain in their original directories.\n\n')
    emit(root / output, intro + '| Case | Mode | Declared model | β | Eligible rungs | Result |\n| --- | ---: | --- | ---: | ---: | --- |\n' + '\n'.join(rows) + '\n', check)


def polynomial(root, analysis, check=False):
    rows = []
    for row in analysis['polynomial_budgets']:
        name = row['case'].removeprefix('Hex.RankBench.')
        budget = f"{row['budget_ns'] / 1e6:.3f}" if row['budget_ns'] is not None else 'pending'
        rows.append(f"| [`{name}`](polynomial/{row['source']}) | {row['native_ns'] / 1e6:.3f} | {budget} | {'yes' if row['hash_agreement'] else 'no'} | {row['verdict']} |")
    emit(root / 'polynomial-verdicts.md', '# Polynomial absolute budgets\n\nAll 60 cases use mode 3. The [policy](polynomial-budget-policy.json) was fixed before the matched stage measurements. Budgets are twice the summed SymPy reference medians, in milliseconds, independent of the child timeout. [Analysis](analysis.json) names every reference and raw block.\n\n| Case | Native ms | Absolute budget ms | Hash agreement | Verdict |\n| --- | ---: | ---: | --- | --- |\n' + '\n'.join(rows) + '\n', check)


def ratios(root, analysis, check=False):
    rows = []
    for row in analysis['rank']['curves']:
        def fmt(value):
            return '—' if value is None else f'{value:.3f}'
        rows.append(f"| `{row['label']}` | {fmt(row['native_ns'] / 1e6 if row['native_ns'] is not None else None)} | {fmt(row['external_ns'] / 1e6 if row['external_ns'] is not None else None)} | {fmt(row['raw_ratio'])} | {fmt(row['adjusted_ratio'])} | {row['successful_pairs']}/6 | {'yes' if row['eligible'] else 'no'} |")
    emit(root / 'comparator-ratios.md', '# Exact-domain rank comparator curves\n\nEvery shared rung appears below. [JSONL](comparator-curves.jsonl) supplies the exact registered names, original raw paths, all paired blocks, and each block’s same-CPU protocol control. Ratios divide the two arm medians; the paired median ratio is also retained. Adjustment subtracts each block’s protocol control before taking the external median. Eligibility requires all six successful pairs, control overhead at most half the external time on every block, and both median times at most ten seconds. Censored and incomplete cases remain visible. All comparators are informational.\n\n| Case | Hex ms | External ms | Raw Hex/external | Adjusted | Successful pairs | Eligible |\n| --- | ---: | ---: | ---: | ---: | ---: | --- |\n' + '\n'.join(rows) + '\n', check)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, default=Path('reports/bench-results/hex-rank-10352'))
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    root = args.data
    analysis = json.loads((root / 'analysis.json').read_text())
    parametric(root, ['integer', 'attribution'], 'integer-verdicts.md', check=args.check)
    parametric(root, ['quotient-large/' + op + rank for rank in ('Full', 'Deficient')
                     for op in ('produce', 'prepare', 'finish', 'check')], 'quotient-verdicts.md', True, args.check)
    polynomial(root, analysis, args.check)
    ratios(root, analysis, args.check)


if __name__ == '__main__':
    main()
