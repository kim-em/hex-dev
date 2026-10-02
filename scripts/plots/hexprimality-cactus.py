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


def plot_direct(data: dict, out_dir: Path, record_name: str = "unspecified") -> None:
    """Show kernel growth by input as well as the independently sorted cactus."""
    fig, axes = plt.subplots(1, 2, figsize=(11, 5), sharey=True)
    cases = data['cases']
    for system, label in [('hex', 'Hex'), ('primecert', 'PrimeCert')]:
        points = []
        color = None
        for index, case in enumerate(cases):
            rows = [r for r in data['rows'] if r['system'] == system and r['case'] == case['name']]
            if len(rows) != data['blocks'] or any(r['status'] != 'ok' for r in rows):
                continue
            values = [r['kernel_nanos']/1e6 for r in rows]
            points.append((index, statistics.median(values), case['name'], values))
        line, = axes[0].plot([x for x, _, _, _ in points], [y for _, y, _, _ in points],
                             marker='o', label=label)
        color = line.get_color()
        for x, _, _, values in points:
            axes[0].scatter([x]*len(values), values, color=color, alpha=.45, s=15)
        ordered = sorted(points, key=lambda p: p[1])
        axes[1].plot(range(1, len(ordered)+1), [y for _, y, _, _ in ordered],
                     marker='o', color=color, label=f'{label} ({len(ordered)}/{len(cases)})')
        for rank, (_, elapsed, name, _) in enumerate(ordered, 1):
            if name == 'Curve25519':
                axes[1].annotate('25519', (rank, elapsed), xytext=(4, 6),
                                 textcoords='offset points', color=color, fontsize=9)
    axes[0].set_xticks(range(len(cases)), [c['name'].replace('family-', '') for c in cases],
                       rotation=35, ha='right')
    axes[0].set_xlabel('Input (family labels give bit length)')
    axes[0].set_ylabel('Kernel check, milliseconds (log scale)')
    axes[0].set_title(f'Same inputs; dots retain all {data["blocks"]} trials')
    axes[1].set_xlabel('Instances checked, independently sorted')
    axes[1].set_xticks(range(1, len(cases)+1))
    axes[1].set_title('Direct kernel cactus')
    for ax in axes:
        ax.set_yscale('log')
        ax.grid(True, which='both', alpha=.2)
        ax.legend()
    fig.suptitle('Supplied certificates: actual kernel checking time')
    supplied = data.get('supplied_hex_sources', {})
    coverage = (f'{", ".join(supplied)}: supplied certificates in both systems; construction coverage is measured separately.'
                if supplied else
                'Curve448: PrimeCert supplied certificate; Hex has no generated certificate in this corpus.')
    compact = (' PrimeCert uses matching Pocklington factors.'
               if data.get('supplied_primecert_sources') else '')
    versions = {
        system: data['versions'][system]['toolchain'].rsplit(':', 1)[-1].removeprefix('v')
        for system in ('hex', 'primecert')
    }
    fig.text(.5, .035,
             'Kernel.check of full local proof bodies; auxiliary proofs expanded; imports/elaboration excluded.\n'
             f'Hex Lean {versions["hex"]} / PrimeCert Lean {versions["primecert"]}. '
             f'{data["blocks"]} AB/BA pairs; all samples retained.{compact}\n'
             + coverage,
             ha='center', fontsize=8)
    fig.text(.5, .008, f'Record: {record_name}', ha='center', fontsize=7)
    fig.tight_layout(rect=(0, .15, 1, .96))
    for ext in ['svg', 'png']:
        output = out_dir/f'hex-primality-kernel-direct.{ext}'
        fig.savefig(output, dpi=160, metadata={'Date': None} if ext == 'svg' else {})
        if ext == 'svg':
            output.write_text('\n'.join(line.rstrip() for line in output.read_text().splitlines())+'\n')
    plt.close(fig)


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('data', type=Path)
    p.add_argument('--out-dir', type=Path, default=Path('reports/figures'))
    p.add_argument('--direct-kernel', type=Path)
    args = p.parse_args()
    data = json.loads(args.data.read_text())
    interpreted = 'interpreter' in data.get('hex_execution_mode', '')
    hex_label = 'Hex interpreted tactic search' if interpreted else 'Hex native exact decision'
    args.out_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({'svg.hashsalt': 'hex-primality-cactus', 'font.size': 10})
    if args.direct_kernel:
        plot_direct(json.loads(args.direct_kernel.read_text()), args.out_dir, args.direct_kernel.name)
    charts = [
        ('native', [('hex', hex_label), ('flint', 'FLINT is_prime'),
                    ('pari', 'PARI isprime')], len(data['cases'])),
        ('kernel', [('hex', 'Hex generated certificate'), ('primecert', 'PrimeCert supplied certificate')],
         sum('primecert' in c for c in data['cases']))]
    if 'end_to_end' in data:
        charts.append(('complete', [('hex', hex_label),
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
                    offset = (9 if system == 'hex_complete' else -14) if phase == 'complete' else (7 if system == 'hex' else -14)
                    ax.annotate('25519', (rank, elapsed), xytext=(4, offset),
                                textcoords='offset points', fontsize=8, color=line.get_color())
        ax.set_yscale('log')
        ax.set_xlim(.5, denominator+.5)
        ax.set_xticks(range(1, denominator+1))
        ax.set_xlabel('Instances solved, sorted independently for each system')
        ax.set_ylabel('Median seconds per instance (log scale)')
        ax.set_title({'native': 'Exact primality decisions' if interpreted else 'Native exact primality decisions',
                      'kernel': 'Supplied-certificate replay: fresh Lean builds',
                      'complete': 'Native decision and complete Lean proof'}[phase])
        ax.grid(True, which='both', alpha=.2)
        ax.legend(loc='best', fontsize=9)
        note = {'native': '12 fixed primes; input/imports excluded; two adjacent, reversed trials.',
                'kernel': f"8 fixed primes; {data['timeout']:g}s timeout; Hex Lean 4.34-rc2 / PrimeCert Lean 4.33.0.\n"
                          'Includes imports, literal elaboration and kernel checking; excludes certificate search.',
                'complete': '12 fixed primes. Native: no Lean proof or kernel replay; input/imports excluded.\n'
                            'Full proof: fresh Lake build including search, proof emission, imports and kernel replay.'}[phase]
        if interpreted and phase != 'kernel':
            note += '\nHex search uses the Lean interpreter; FLINT/PARI calls are native.'
        fig.text(.5, .025, note + '\nShared host; all completed samples retained. Missing/failed certificates are unsolved.',
                 ha='center', fontsize=8)
        fig.tight_layout(rect=(0, .11 if phase in ('complete', 'kernel') else .075, 1, 1))
        for ext in ['svg', 'png']:
            output = args.out_dir/f'hex-primality-{phase}-cactus.{ext}'
            fig.savefig(output, dpi=160,
                        metadata={'Date': None} if ext == 'svg' else {})
            if ext == 'svg':
                output.write_text('\n'.join(line.rstrip() for line in output.read_text().splitlines())+'\n')
        plt.close(fig)


if __name__ == '__main__':
    main()
