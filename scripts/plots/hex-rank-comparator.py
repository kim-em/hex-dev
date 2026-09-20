#!/usr/bin/env python3
"""Plot committed HexRank comparator curves; never collect measurements."""
import argparse
import io
import json
from pathlib import Path
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'reports/bench-results/hex-rank-10352/comparator-curves.jsonl'
PANELS = {
    'dense-full-rank': ['Dense'],
    'low-rank-large-coefficients': ['LowRank2At64', 'LowRank8At64', 'LowRank2At1024', 'LowRank8At1024'],
    'rank-deficient-by-construction': ['DeficientMinusOne', 'DeficientHalf', 'DeficientHalfShifted'],
    'polynomial': ['RatPolyFull', 'RatPolyDeficient', 'MvFull', 'MvDeficient'],
}


def coordinates(row):
    case = row['blocks'][0]['native_case']
    match = re.fullmatch(r'Hex.RankBench.Comparison.(Int|Rat).([^.]+).native(\d+)', case)
    if match:
        carrier, panel, n = match.groups()
        return panel, carrier, int(n)
    match = re.fullmatch(r'Hex.RankBench.run(RatPoly|Mv)(Deficient)?Rank(\d+)', case)
    if match:
        carrier, rank, n = match.groups()
        return carrier + (rank or 'Full'), carrier, int(n)
    raise ValueError('unrecognized comparison case: ' + case)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=PANELS, required=True)
    parser.add_argument('--data', type=Path, default=DATA)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', action='store_true', help='Check the committed SVG without changing it.')
    args = parser.parse_args()
    rows = [json.loads(line) for line in args.data.read_text().splitlines()]
    panels = PANELS[args.family]
    cols = min(2, len(panels))
    height = (len(panels) + cols - 1) // cols
    plt.rcParams.update({'svg.hashsalt': 'hex-rank', 'font.size': 10})
    fig, axes = plt.subplots(height, cols, figsize=(6 * cols, 4 * height), squeeze=False)
    for axis, panel in zip(axes.flat, panels):
        panel_rows = [(row, coordinates(row)) for row in rows if coordinates(row)[0] == panel]
        expected = 3 if args.family == 'polynomial' else 18
        if len(panel_rows) != expected or any(not row['attempts_complete'] for row, _ in panel_rows):
            raise ValueError('unfinished declared schedule: ' + panel)
        selected = [(row, coordinate) for row, coordinate in panel_rows if row['eligible']]
        if any(not row['complete'] for row, _ in selected):
            raise ValueError('unfinished six-block curve: ' + panel)
        carriers = sorted({coordinate[1] for _, coordinate in selected})
        expected_carriers = ({'RatPoly'} if panel.startswith('RatPoly') else {'Mv'}) if args.family == 'polynomial' else {'Int', 'Rat'}
        if set(carriers) != expected_carriers:
            raise ValueError('missing eligible comparator for ' + panel)
        for carrier in carriers:
            points = sorted((coordinate[2], row) for row, coordinate in selected if coordinate[1] == carrier)
            if len(points) < 2:
                raise ValueError('fewer than two eligible rungs: ' + panel + '/' + carrier)
            for key, label, style in [('native_ns', 'Hex', '-'), ('external_ns', 'SymPy' if args.family == 'polynomial' else 'FLINT', '--')]:
                axis.plot([n for n, _ in points], [row[key] / 1e6 for _, row in points],
                          marker='o', linestyle=style, label=label + ' ' + carrier)
        axis.set(title=panel, xlabel='Matrix dimension', ylabel='Median per call (ms)', yscale='log')
        axis.grid(True, alpha=.25)
        axis.legend()
    for axis in list(axes.flat)[len(panels):]:
        axis.set_visible(False)
    fig.suptitle('HexRank: ' + args.family + ' — eligible shared-host measurements')
    fig.tight_layout()
    output = args.output or ROOT / 'reports/figures' / f'hex-rank-comparator-{args.family}.svg'
    output.parent.mkdir(parents=True, exist_ok=True)
    metadata = {'Date': None, 'Description': str(args.data.relative_to(ROOT)) if args.data.is_relative_to(ROOT) else args.data.name}
    if output.suffix == '.svg':
        stream = io.StringIO()
        fig.savefig(stream, format='svg', metadata=metadata)
        rendered = '\n'.join(line.rstrip() for line in stream.getvalue().splitlines()) + '\n'
        if args.check:
            if not output.exists() or output.read_text() != rendered:
                raise SystemExit('stale rank figure: ' + str(output))
        else:
            output.write_text(rendered)
    else:
        if args.check:
            parser.error('--check requires SVG output')
        fig.savefig(output, metadata=metadata)
    plt.close(fig)


if __name__ == '__main__':
    main()
