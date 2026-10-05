#!/usr/bin/env python3
"""Plot kernel-replayed proof coverage from one frozen prime-corpus sweep."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--report', type=Path, required=True)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True, help='PNG path; also writes an SVG')
    args = p.parse_args()
    if args.output.exists() or args.output.with_suffix('.svg').exists():
        p.error('retain existing plots; choose a new output path')
    data = json.loads(args.report.read_text())
    manifest = json.loads(args.manifest.read_text())
    assert data['complete'] and not manifest['partial']
    assert manifest['reports'][args.report.name] == hashlib.sha256(args.report.read_bytes()).hexdigest()
    checked = {(x['report'], x['sample']) for x in manifest['links']}
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    fig, axes = plt.subplots(2, 2, figsize=(10, 7), sharex=True, sharey=True)
    styles = [('baseline', 'Hex current', '#737373'),
              ('interleaved', 'Hex interleaved', '#1764ab'),
              ('primecert', 'PrimeCert + SymPy', '#bd6513')]
    for bits, ax in zip([128, 256, 384, 512], axes.flat):
        n = sum(c['bits'] == bits for c in data['cases'])
        for profile, label, color in styles:
            times = []
            for i, row in enumerate(data['samples']):
                if row['subject'].bit_length() != bits or row['profile'] != profile:
                    continue
                if row.get('result', {}).get('status') in ['success', 'generated']:
                    assert (args.report.name, i) in checked
                    times.append(row['wall_ns'] / 1e9)
            times.sort()
            ax.step([0.01, *times, 180], [0, *range(1, len(times) + 1), len(times)],
                    where='post', color=color, label=f'{label}: {len(times)}/{n}', linewidth=2)
        ax.set_title(f'{bits}-bit primes')
        ax.set_xscale('log')
        ax.set_xlim(0.01, 180)
        ax.set_ylim(0, n + 2)
        ax.grid(alpha=0.2)
        ax.legend(loc='upper left', fontsize=8)
    fig.suptitle('Kernel-checked primality certificates found', fontsize=15)
    fig.supxlabel('Elapsed generation time (seconds, logarithmic scale)', y=0.055)
    fig.supylabel('Number of prime subjects proved')
    fig.text(0.5, 0.012, 'One run per fresh subject; 180-second process limit. Shared-host observations; replay time excluded.',
             ha='center', fontsize=8)
    fig.tight_layout(rect=(0.025, 0.11, 1, 0.96))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.output, dpi=180)
    fig.savefig(args.output.with_suffix('.svg'))


if __name__ == '__main__':
    main()
