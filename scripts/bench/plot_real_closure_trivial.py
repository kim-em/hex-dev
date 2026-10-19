#!/usr/bin/env python3
"""Plot retained distinct-root route comparisons without fitting a timing model."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('analysis', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    data = json.loads(args.analysis.read_text())
    if data.get('suite') != 'distinct' or data.get('observations') != 96:
        parser.error('expected the completed registered distinct-root comparison')
    cases = {row['case']: row for row in data['comparisons']}
    expected = {family + str(size) for family in ('Rational', 'Quadratic') for size in (2, 4, 6, 8)}
    if set(cases) != expected:
        parser.error('comparison has different registered cases')
    source = data['source']
    plt.rcParams.update({'svg.hashsalt': source, 'pdf.fonttype': 42,
                         'font.size': 9, 'axes.spines.top': False,
                         'axes.spines.right': False})
    args.destination.mkdir(parents=True, exist_ok=True)
    outputs = []
    for stem, field, divisor, ylabel, logarithmic in (
        ('root-routes', '_ms', 1, 'Complete roots + exact consumer (ms)', True),
        ('root-memory', '_maximum_resident_set_kib', 1024,
         'Whole-arm maximum RSS (MiB)', False),
    ):
        fig, axes = plt.subplots(1, 2, figsize=(10, 4.4), sharey=True)
        for ax, family, title in zip(axes, ('Rational', 'Quadratic'),
                                     ('Rational roots 1,...,N', 'Quadratic factors X²-p')):
            for arm, offset, color, label in (
                ('generic', -.10, '#2864ad', 'Generic + conversion'),
                ('canonical', .10, '#c96719', 'Canonical backend'),
            ):
                sizes = (2, 4, 6, 8)
                summaries = [cases[family + str(size)][arm + field] for size in sizes]
                xs = [size + offset for size in sizes]
                medians = [row['median']/divisor for row in summaries]
                errors = [[(row['median']-row['minimum'])/divisor for row in summaries],
                          [(row['maximum']-row['median'])/divisor for row in summaries]]
                for x, row in zip(xs, summaries):
                    if row['samples'] != 6 or len(row['values']) != 6:
                        parser.error('a case lost one of its six retained batches')
                    ax.scatter([x+(trial-2.5)*.015 for trial in range(6)],
                               [value/divisor for value in row['values']],
                               color=color, s=11, alpha=.4, zorder=2)
                ax.errorbar(xs, medians, yerr=errors, color=color, marker='o',
                            markersize=4, linewidth=1.2, capsize=3, label=label, zorder=3)
            if logarithmic:
                ax.set_yscale('log')
            else:
                ax.set_ylim(bottom=0)
            ax.set_title(title)
            ax.set_xticks((2, 4, 6, 8))
            ax.set_xlim(1.5, 8.5)
            ax.set_xlabel('Distinct real roots = input degree')
            ax.grid(axis='y', alpha=.2)
        axes[0].set_ylabel(ylabel)
        axes[0].legend(frameon=False, fontsize=8)
        scope = ('Whole-arm RSS includes driver, all 14 installed inputs, warmup and children.'
                 if not logarithmic else
                 'Six paired batch estimates; markers are medians, bars show full ranges. No scaling fit.')
        fig.suptitle('Complete root routes on rational inputs', fontsize=12)
        fig.text(.5, .025, scope + '\nSource ' + source[:10] + ' on ' + data['host'],
                 ha='center', va='bottom', fontsize=8)
        fig.tight_layout(rect=(0, .12, 1, .94))
        for extension in ('png', 'svg', 'pdf'):
            path = args.destination / (stem + '.' + extension)
            description = 'Retained complete-root comparison at source ' + source
            metadata = ({'CreationDate': None, 'ModDate': None, 'Subject': description}
                        if extension == 'pdf' else
                        {'Date': None, 'Description': description} if extension == 'svg' else
                        {'Description': description})
            fig.savefig(path, dpi=180, metadata=metadata)
            outputs.append(dict(path=path.name, sha256=digest(path)))
        plt.close(fig)
    provenance = dict(source=source, analysis_sha256=digest(args.analysis),
                      plot_sha256=digest(__file__), matplotlib=matplotlib.__version__,
                      python=sys.version, runtime_library_path=os.environ.get("LD_LIBRARY_PATH"),
                      command=sys.argv, figures=outputs)
    (args.destination / 'figure-source.json').write_text(json.dumps(provenance, indent=2)+'\n')


if __name__ == '__main__':
    main()
