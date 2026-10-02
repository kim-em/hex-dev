#!/usr/bin/env python3
"""Render retained kernel attribution without filtering completed samples."""
import json
import statistics
import tarfile
from pathlib import Path


def sample_ms(sample):
    value, unit = sample['kernel_timer'][-1]
    return float(value) * {'ms': 1, 's': 1000, 'μs': .001, 'µs': .001, 'ns': .000001}[unit]


def render(path: Path) -> str:
    with tarfile.open(path, 'r:gz') as archive:
        records = {name: json.load(archive.extractfile(name + '/record.json'))
                   for name in {m.name.split('/')[0] for m in archive.getmembers()}
                   if name.startswith('attribution-')}
    link = 'data/hex-kronecker-mathlib/' + path.name
    text = f'''## Kernel attribution

[All attribution samples, compiler logs, runner text, and measured source archives]({link})
are retained. Each controlled comparison uses six adjacent AB/BA pairs on one
automatically leased CPU. Tables report Lean's aggregate `type checking` timer
in milliseconds, with `profiler.threshold=0`. No import baseline is subtracted
from this timer. The paired gain is reference minus candidate; MAD describes
variation across the six gains. Different comparisons ran on different leased
CPUs and execution segments, so their absolute medians are not additive.

The cap comparison changes only the diagnostic budget from 16,777,216 to
65,536 bits on the original checker; all seven identities fit both budgets.
This isolates the large threshold literal without changing the shipping
budget or probes. Root-only replay then removes size reporting and budget
checking entirely. Direct recursion also uses primitive arithmetic and the
bit-length preflight, whose equality with the public size report is proved.
The final translation comparison changes only `fromGrind` to a direct recursor.

'''
    comparisons = [
        ('cap', 'Threshold literal: original budget → diagnostic smaller cap'),
        ('root', 'Kernel form: original checker → root-only replay'),
        ('recursion', 'Traversals: root-only replay → direct recursors and primitives'),
        ('translation', 'Translation: equation compiler → direct `fromGrind` recursor'),
        ('determinant', 'Determinants: original checker → direct root-only replay'),
        ('determinant-final', 'Determinants: original checker → final translation and replay'),
    ]
    for name, title in comparisons:
        record = records['attribution-' + name + '-pairs']
        if not record['sources_unchanged']:
            raise ValueError(f'changed sources in {name}')
        text += f'### {title}\n\n'
        text += '| Case | Reference ms | Candidate ms | Paired gain ms | MAD ms |\n'
        text += '| --- | ---: | ---: | ---: | ---: |\n'
        improved = total = 0
        for case in dict.fromkeys(s['case'] for s in record['samples']):
            arms = {}
            for arm in ['reference', 'candidate']:
                samples = [s for s in record['samples'] if s['case'] == case and s['arm'] == arm]
                if len(samples) != 6 or any(s['returncode'] for s in samples):
                    raise ValueError(f'incomplete comparison: {name} {case} {arm}')
                arms[arm] = {s['trial']: sample_ms(s) for s in samples}
            gains = [arms['reference'][t] - arms['candidate'][t] for t in range(1, 7)]
            center = statistics.median(gains)
            mad = statistics.median(abs(g - center) for g in gains)
            values = [statistics.median(arms[a].values()) for a in ['reference', 'candidate']]
            total += 1
            improved += values[1] <= values[0]
            text += f'| {case} | ' + ' | '.join(f'{v:.3f}' for v in [*values, center, mad]) + ' |\n'
        text += '\n'
        if name == 'determinant-final':
            determinant_result = f'{improved}/{total}'
    translation = records['attribution-translation-pairs']
    smallest = [sample_ms(s) for s in translation['samples']
                if s['case'] == 'GridK2D2' and s['arm'] == 'candidate']
    text += (f'The final `GridK2D2` kernel median is **{statistics.median(smallest):.3f} ms** '
             f'(range {min(smallest):.3f}–{max(smallest):.3f} ms). The 5 ms kernel-median target is '
             f"**{'passed' if statistics.median(smallest) <= 5 else 'not passed'}**. "
             'Individual shared-host observations remain in the record. '
             f'{determinant_result} determinant kernel medians are no larger in the final '
             'controlled comparison. The full final sweep supplies the '
             'shipping fresh-module results.\n\n')
    text += '''### Plan selection and reflection

Exploratory single profiles compared recomputing the root plan against passing
its degree vector and digit width and validating them. `GridK2D2` took 3.09 ms
with recomputation and 3.58 ms with the supplied plan; other cases were mixed.
The implementation recomputes the plan, avoiding a larger certificate without
a demonstrated consistent gain. These exploratory observations are not six-pair
estimates; the archive retains every baseline, root, direct, recomputed, and
supplied-plan profile and its source state.

The instrumented `GridK2D2` reflection profile totals about **3.92 ms** across
exclusive nested timers: session/setup/sealing 0.155 ms, left reification
0.984 ms, right reification 0.254 ms, `contextExpr` 0.032 ms, Sym.Arith
canonicalization 1.04 ms, and Sym.Arith instance inference 1.45 ms. Within
instance inference, the recorded calls include `Grind.CommRing` 0.026 ms,
`IsCharP` 0.167 ms, `NatModule` 0.107 ms, `NoNatZeroDivisors` 0.814 ms,
and `Field` 0.218 ms. Repeated `CommRing` queries cost only 0.0044 and
0.0027 ms. The outer Mathlib `CommRing` query costs another 0.098 ms.
These numbers are from the retained `attribution-recomputed/GridK2D2.log`;
the nested instance entries are components, not additional costs to sum.

The session already shares classification and atoms across both sides.
Removing characteristic, zero-divisor, or field classification would alter
Sym.Arith's retained ring classification; it is not an avoidable duplicate
session cost under hex-reflect's contract. Context construction is negligible.
No reflection contract or default tactic chain changes. The remaining roughly
4 ms reflection cost explains why reducing kernel work alone need not put
every small identity below `ring`; the full table reports that outcome without
changing any probe.

'''
    return text
