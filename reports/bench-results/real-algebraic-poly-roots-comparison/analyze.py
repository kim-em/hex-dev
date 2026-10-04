#!/usr/bin/env python3
"""Display all retained root observations and adjacent exact-result pairs."""
from pathlib import Path
import csv
import json
from statistics import median
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
meta = json.loads((HERE/'metadata.json').read_text())
if not (meta['source_unchanged'] and meta['binary_unchanged']):
    raise SystemExit('Source or executable changed during collection')
observations, failed = [], []
for arm in meta['arms']:
    output = HERE/arm['output']
    if not output.exists():
        failed.append({**arm, 'reason': 'no result file'}); continue
    r = json.loads(output.read_text())['results'][0]
    if arm['exit_code'] or r['budget_truncated'] or any(p['status'] != 'ok' for p in r['points']):
        failed.append({**arm, 'result': r}); continue
    if r['expected_hash_check']['status'] != 'match' or not r['hashes_agree']:
        raise ValueError('Complete expected fingerprint check failed')
    observations.append({**arm, 'per_call_nanos': median(
        p['total_nanos']/p['inner_repeats'] for p in r['points']),
        'hash': r['observed_hash'], 'peak_rss_kb': max(p['peak_rss_kb'] for p in r['points'])})

pairs, summary = [], []
for family, degrees in meta['families'].items():
    for degree in degrees:
        for backend in ['Flint', 'Z3']:
            joined = []
            for block in range(4):
                group = [p for p in observations if p['family'] == family and p['degree'] == degree
                         and p['comparator'] == backend and p['block'] == block]
                n = next((p for p in group if p['backend'] == 'Native'), None)
                e = next((p for p in group if p['backend'] == backend and not p['protocol']), None)
                c = next((p for p in group if p['protocol']), None)
                if not (n and e and c): continue
                if not n['hash'] == e['hash'] == c['hash']:
                    raise ValueError('Complete fingerprints differ between paired arms')
                nt, et, ct = [p['per_call_nanos'] for p in [n, e, c]]
                joined.append(dict(family=family, degree=degree, backend=backend, block=block,
                    native_nanos=nt, external_nanos=et, protocol_nanos=ct,
                    raw_ratio=nt/et, adjusted_ratio=nt/(et-ct) if et > ct else None))
            pairs.extend(joined)
            if joined:
                adjusted = [p['adjusted_ratio'] for p in joined if p['adjusted_ratio'] is not None]
                summary.append(dict(family=family, degree=degree, backend=backend, complete_pairs=len(joined),
                    native_ms=median(p['native_nanos'] for p in joined)/1e6,
                    external_ms=median(p['external_nanos'] for p in joined)/1e6,
                    protocol_us=median(p['protocol_nanos'] for p in joined)/1e3,
                    raw_ratio=median(p['raw_ratio'] for p in joined),
                    adjusted_ratio=median(adjusted) if adjusted else None,
                    adjusted_pairs=len(adjusted),
                    protocol_fraction=median(p['protocol_nanos'] for p in joined)/median(p['external_nanos'] for p in joined)))
expected = 4 * sum(map(len, meta['families'].values())) * 2 * 3
result = dict(source_commit=meta['source_commit'], expected_arms=expected,
    collected_arms=len(meta['arms']), completed_observations=observations,
    failed_or_censored=failed, pairs=pairs, summary=summary, classification=meta['classification'])
(HERE/'analysis.json').write_text(json.dumps(result, indent=2)+'\n')
with (HERE/'summary.csv').open('w') as f:
    w = csv.DictWriter(f, fieldnames=list(summary[0]), lineterminator='\n')
    w.writeheader(); w.writerows(summary)

plt.rcParams['svg.hashsalt'] = 'hex'
fig, axes = plt.subplots(2, 2, figsize=(12, 8))
fig.suptitle('Actual real-algebraic polynomial roots: Hex, Z3 RCF and FLINT qqbar', fontsize=15)
for row, (family, degrees) in enumerate(meta['families'].items()):
    time_ax, ratio_ax = axes[row]
    for backend, label in [('Native', 'Hex real-algebraic'), ('Z3', 'Z3 RCF'), ('Flint', 'FLINT qqbar driver')]:
        xs, ys, low, high = [], [], [], []
        for degree in degrees:
            values = [p['per_call_nanos']/1e6 for p in observations if p['family'] == family
                      and p['degree'] == degree and p['backend'] == backend and not p['protocol']]
            if values:
                xs.append(degree); ys.append(median(values)); low.append(min(values)); high.append(max(values))
        line, = time_ax.plot(xs, ys, 'o-', label=label, lw=2)
        time_ax.fill_between(xs, low, high, color=line.get_color(), alpha=.13)
        for p in observations:
            if p['family'] == family and p['backend'] == backend and not p['protocol']:
                time_ax.scatter(p['degree'], p['per_call_nanos']/1e6, s=12, color=line.get_color(), alpha=.3)
    for backend in ['Z3', 'Flint']:
        rows = [s for s in summary if s['family'] == family and s['backend'] == backend]
        line, = ratio_ax.plot([s['degree'] for s in rows], [s['raw_ratio'] for s in rows],
                              'o-', label=f'{backend}: raw', lw=2)
        adjusted = [s for s in rows if s['adjusted_ratio'] is not None]
        ratio_ax.plot([s['degree'] for s in adjusted], [s['adjusted_ratio'] for s in adjusted],
                      '--', color=line.get_color(), label=f'{backend}: protocol-adjusted')
    ratio_ax.axhline(1, color='#444444', ls=':', lw=1)
    for ax in [time_ax, ratio_ax]:
        ax.set_xscale('log', base=2); ax.set_xticks(degrees, degrees)
        ax.set_yscale('log'); ax.grid(alpha=.2); ax.legend(fontsize=8)
        ax.set_xlabel('Polynomial degree n (coefficient height fixed)')
    time_ax.set_title('Xⁿ − 2' if family == 'Rational' else 'Xⁿ − √2 (n=1: one root; n≥2: two roots)')
    time_ax.set_ylabel('Root operation per call (ms, log scale)')
    ratio_ax.set_ylabel('Paired Hex / external ratio (>1: Hex slower)')
fig.text(.015, .015,
    f"Shared host {meta['host']}, leased CPU {meta['cpu']}; 4 adjacent AB/BA pairs per backend/rung. All samples retained; no fitted model.\n"
    "Prepared coefficients; solving, ordering and fingerprints timed. External exact-annihilation checks, JSON and cleanup included.\n"
    "Separate unpinned degree-16 rational and degree-8 quadratic probes hit a 60 s whole-child cap; no numerical operation time inferred.\n"
    f"Source {meta['source_commit'][:9]}; protocol adjustment is a framing control. Comparison failures/censored arms: {len(failed)}; collected {len(meta['arms'])}/{expected}.", fontsize=8)
fig.tight_layout(rect=(0, .11, 1, .96))
for fmt in ['png', 'svg', 'pdf']:
    p = HERE/f'comparison.{fmt}'
    metadata = {'Date': None} if fmt == 'svg' else {'CreationDate': None} if fmt == 'pdf' else None
    fig.savefig(p, dpi=170, metadata=metadata)
    if fmt == 'svg':
        p.write_text('\n'.join(line.rstrip() for line in p.read_text().splitlines())+'\n')
print(json.dumps(summary, indent=2))
