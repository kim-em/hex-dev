#!/usr/bin/env python3
"""Plot the retained primality comparison; failures never become fast solves."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import statistics
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('data', type=Path)
    p.add_argument('--out-dir', type=Path, default=Path('reports/figures'))
    args = p.parse_args()
    data = json.loads(args.data.read_text())
    args.out_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({'svg.hashsalt': 'hex-primality-cactus', 'font.size': 10})
    for phase, systems, denominator in [
        ('native', [('hex', 'Hex construction + self-check'), ('flint', 'FLINT is_prime'),
                    ('pari', 'PARI isprime')], len(data['cases'])),
        ('kernel', [('hex', 'Hex generated certificate'), ('primecert', 'PrimeCert supplied certificate')],
         sum('primecert' in c for c in data['cases']))]:
        fig, ax = plt.subplots(figsize=(8, 5))
        for system, label in systems:
            points = []
            for case in data['cases']:
                rows = [r for r in data[phase] if r['system'] == system and r['case'] == case['name']
                        and (phase == 'native' or r.get('arm') == 'replay' or r['status'] == 'no-certificate')]
                if len(rows) != data['blocks'] or any(r['status'] != 'ok' for r in rows):
                    continue
                values = [r['result']['nanos'] / 1e9 if phase == 'native' else r['seconds'] for r in rows]
                points.append((statistics.median(values), case['name']))
            points.sort()
            xs = list(range(1, len(points)+1))
            line, = ax.plot(xs, [t for t, _ in points], marker='o', label=f'{label} ({len(points)}/{denominator})')
            for rank, (elapsed, name) in enumerate(points, 1):
                if name == 'Curve25519':
                    ax.annotate('25519', (rank, elapsed), xytext=(4, 7 if system == 'hex' else -14),
                                textcoords='offset points', fontsize=8, color=line.get_color())
        if phase == 'kernel':
            ax.axhline(data['timeout'], color='gray', linestyle=':', label=f"{data['timeout']:g}s process timeout")
        ax.set_yscale('log')
        ax.set_xlim(.5, denominator+.5)
        ax.set_xticks(range(1, denominator+1))
        ax.set_xlabel('Instances solved, sorted independently for each system')
        ax.set_ylabel('Median seconds per instance (log scale)')
        ax.set_title('Native proven primality' if phase == 'native' else 'Lean kernel-checked certificate replay')
        ax.grid(True, which='both', alpha=.2)
        ax.legend(loc='best', fontsize=9)
        note = ('12 fixed primes; input/imports excluded; two adjacent, reversed trials.' if phase == 'native'
                else '8 fixed primes; fresh Lake builds; Hex Lean 4.34-rc2 / PrimeCert Lean 4.33.0.')
        fig.text(.5, .025, note + '\nShared host; all completed samples retained. Missing/failed certificates are unsolved.',
                 ha='center', fontsize=8)
        fig.tight_layout(rect=(0, .075, 1, 1))
        for ext in ['svg', 'png']:
            fig.savefig(args.out_dir/f'hex-primality-{phase}-cactus.{ext}', dpi=160,
                        metadata={'Date': None} if ext == 'svg' else {})
        plt.close(fig)


if __name__ == '__main__':
    main()
