#!/usr/bin/env python3
"""Plot retained Bareiss comparator medians; never collect new measurements."""
import argparse
import json
from pathlib import Path
import re

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
FAMILIES = {
    'structured-bareiss-determinant': [('Det', None)],
    'scalar-carriers': [('Rat', None), ('Mod', None)],
    'dense-polynomial-carriers': [(c, ('D', d)) for c in ('DenseRat', 'DenseMod', 'ZPoly')
                                for d in (1, 2, 3)],
    'multivariate-carriers': [(c, ('T', t)) for c in ('MvInt', 'MvRat') for t in (2, 3, 4)],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=FAMILIES, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    integer = args.family == 'structured-bareiss-determinant'
    source = ROOT / 'reports/bench-results' / (
        'hex-bareiss-f4f013c-issue9804-warmed.json' if integer
        else 'hex-bareiss-carriers-571e797e3.json')
    data = json.loads(source.read_text())
    results = data['results'] if integer else [
        result for run in data['runs'] for result in run['export']['results']]
    panels = FAMILIES[args.family]
    cols = min(3, len(panels))
    rows = (len(panels) + cols - 1) // cols
    plt.rcParams.update({'svg.hashsalt': 'hex-bareiss', 'font.size': 10})
    fig, axes = plt.subplots(rows, cols, figsize=(5 * cols, 3.8 * rows), squeeze=False)
    for ax, (carrier, parameter) in zip(axes.flat, panels):
        suffix = '' if parameter is None else ''.join(map(str, parameter))
        for arm, label in [('Bareiss', 'Hex'), ('FlintBareiss' if integer else 'Oracle',
                                              'FLINT' if integer or parameter is None else 'SymPy')]:
            pattern = re.compile(r'Hex.BareissBench.run' + arm + carrier +
                                 ('' if integer else 'N') + r'(\d+)' + suffix)
            points = sorted((int(match[1]), r['median_nanos'] / 1000)
                            for r in results if (match := pattern.fullmatch(r['function'])))
            if len(points) < 2:
                raise ValueError(f'missing comparison curve: {carrier} {suffix} {arm}')
            ax.plot(*zip(*points), marker='o', label=label)
        ax.set(title=carrier + (f' ({suffix})' if suffix else ''),
               xlabel='Matrix dimension n', ylabel='Median per call (µs)', yscale='log')
        ax.grid(True, alpha=.25)
        ax.legend()
    fig.suptitle('Bareiss: ' + args.family + ' — retained shared-host measurements')
    fig.tight_layout()
    output = args.output or ROOT / 'reports/figures' / f'hex-bareiss-comparator-{args.family}.svg'
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, metadata={'Date': None, 'Description': str(source.relative_to(ROOT))})


if __name__ == '__main__':
    main()
