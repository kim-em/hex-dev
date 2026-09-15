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
    charts = [
        ('native', [('hex', 'Hex native exact decision'), ('flint', 'FLINT is_prime'),
                    ('pari', 'PARI isprime')], len(data['cases'])),
        ('kernel', [('hex', 'Hex generated certificate'), ('primecert', 'PrimeCert supplied certificate')],
         sum('primecert' in c for c in data['cases']))]
    if 'end_to_end' in data:
        charts.append(('complete', [('hex', 'Hex native exact decision'),
                                   ('flint', 'FLINT native is_prime'),
                                   ('pari', 'PARI native isprime'),
                                   ('hex_complete', 'Hex primality?: construct + kernel check')],
                       len(data['cases'])))
    for phase, systems, denominator in charts:
        fig, ax = plt.subplots(figsize=(8, 5))
        for system, label in systems:
            points = []
            source_phase = ('end_to_end' if system == 'hex_complete' else 'native') if phase == 'complete' else phase
            source_system = 'hex' if system == 'hex_complete' else system
            for case in data['cases']:
                rows = [r for r in data[source_phase] if r['system'] == source_system and r['case'] == case['name']
                        and (source_phase == 'native' or
                             r.get('arm') == ('complete' if source_phase == 'end_to_end' else 'replay') or
                             r['status'] == 'no-certificate')]
                if len(rows) != data['blocks'] or any(r['status'] != 'ok' for r in rows):
                    continue
                values = [r['result']['nanos'] / 1e9 if source_phase == 'native' else r['seconds'] for r in rows]
                points.append((statistics.median(values), case['name']))
            points.sort()
            xs = list(range(1, len(points)+1))
            line, = ax.plot(xs, [t for t, _ in points], marker='o',
                            linestyle='--' if system == 'hex_complete' else '-',
                            label=f'{label} ({len(points)}/{denominator})')
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
        ax.set_title({'native': 'Native exact primality decisions',
                      'kernel': 'Lean kernel-checked certificate replay (supplied literals)',
                      'complete': 'Native decision and complete Lean proof'}[phase])
        ax.grid(True, which='both', alpha=.2)
        ax.legend(loc='best', fontsize=9)
        note = {'native': '12 fixed primes; input/imports excluded; two adjacent, reversed trials.',
                'kernel': '8 fixed primes; fresh Lake builds; Hex Lean 4.34-rc2 / PrimeCert Lean 4.33.0.',
                'complete': '12 fixed primes. Native: no Lean proof or kernel replay; input/imports excluded.\n'
                            'Full proof: fresh Lake build including search, proof emission, imports and kernel replay.'}[phase]
        fig.text(.5, .025, note + '\nShared host; all completed samples retained. Missing/failed certificates are unsolved.',
                 ha='center', fontsize=8)
        fig.tight_layout(rect=(0, .11 if phase == 'complete' else .075, 1, 1))
        for ext in ['svg', 'png']:
            output = args.out_dir/f'hex-primality-{phase}-cactus.{ext}'
            fig.savefig(output, dpi=160,
                        metadata={'Date': None} if ext == 'svg' else {})
            if ext == 'svg':
                output.write_text('\n'.join(line.rstrip() for line in output.read_text().splitlines())+'\n')
        plt.close(fig)


if __name__ == '__main__':
    main()
