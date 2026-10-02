#!/usr/bin/env python3
"""Summarize all retained lean-bench samples; fail on any incomplete case."""
import json
from pathlib import Path
from statistics import median
here=Path(__file__).resolve().parent
rows=[]
for case in range(12):
    times={'each':[], 'batch':[]}
    for block in range(6):
        data=json.loads((here/'results'/'timing'/f'case{case:02}-block{block}.json').read_text())['results']
        expected=[f'each{case}',f'batch{case}']
        if block%2: expected.reverse()
        assert [r['function'] for r in data] == expected
        assert len({r['observed_hash'] for r in data}) == 1
        for r in data:
            assert r['hashes_agree'] and not r['budget_truncated']
            assert len(r['points']) == 1 and r['points'][0]['status'] == 'ok'
            arm='batch' if r['function'].startswith('batch') else 'each'
            times[arm].append(r['median_nanos']/1e6)
    ratios=[a/b for a,b in zip(times['each'],times['batch'])]
    rows.append(dict(case=case,descriptor='minimal' if case<6 else 'reducible',
                     shared=case%6>=3,n=[4,8,16][case%3],
                     each_ms=median(times['each']),batch_ms=median(times['batch']),
                     paired_ratio=median(ratios),ratio_min=min(ratios),ratio_max=max(ratios)))
(here/'results'/'summary.json').write_text(json.dumps(rows,indent=2)+'\n')
print('| Descriptor | Coefficients | Length | Product, scalar packing (ms) | Batched (ms) | Paired speedup (range) |')
print('|---|---|---:|---:|---:|---:|')
for r in rows:
    print(f"| {r['descriptor']} | {'shared factor' if r['shared'] else 'generic'} | {r['n']} | {r['each_ms']:.3f} | {r['batch_ms']:.3f} | {r['paired_ratio']:.2f}× ({r['ratio_min']:.2f}–{r['ratio_max']:.2f}) |")
