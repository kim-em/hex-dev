#!/usr/bin/env python3
"""Join every adjacent frozen-executable pair without a host-load filter."""
from pathlib import Path
import json
from statistics import median

HERE = Path(__file__).resolve().parent
meta = json.loads((HERE/'metadata.json').read_text())
if not (meta['source_unchanged'] and meta['binary_unchanged']):
    raise SystemExit('Source or frozen executable changed')
pairs, summary, failed = [], [], []
for family, degrees in meta['families'].items():
    for degree in degrees:
        joined = []
        for block in range(4):
            observed = []
            for arm in ['Before', 'After']:
                a = next(a for a in meta['arms'] if a['family'] == family and a['degree'] == degree
                         and a['block'] == block and a['arm'] == arm)
                path = HERE/a['output']
                if not path.exists():
                    failed.append({**a, 'reason': 'no result file'}); continue
                r = json.loads(path.read_text())['results'][0]
                if a['exit_code'] or r['budget_truncated'] or any(p['status'] != 'ok' for p in r['points']):
                    failed.append({**a, 'result': r}); continue
                if r['expected_hash_check']['status'] != 'match' or not r['hashes_agree']:
                    raise ValueError('Complete expected fingerprint failed')
                observed.append((median(p['total_nanos']/p['inner_repeats'] for p in r['points']),
                                 r['observed_hash']))
            if len(observed) != 2: continue
            (before, bh), (after, ah) = observed
            if bh != ah: raise ValueError('Complete result fingerprints differ')
            joined.append(dict(family=family, degree=degree, block=block,
                before_nanos=before, after_nanos=after, ratio=before/after, hash=bh))
        pairs.extend(joined)
        if joined:
            summary.append(dict(family=family, degree=degree, complete_pairs=len(joined),
                before_ms=median(p['before_nanos'] for p in joined)/1e6,
                after_ms=median(p['after_nanos'] for p in joined)/1e6,
                median_adjacent_ratio=median(p['ratio'] for p in joined),
                min_adjacent_ratio=min(p['ratio'] for p in joined),
                max_adjacent_ratio=max(p['ratio'] for p in joined)))
(HERE/'analysis.json').write_text(json.dumps(dict(summary=summary, pairs=pairs,
    collected_arms=len(meta['arms']), expected_arms=16, failed_or_censored=failed), indent=2)+'\n')
print(json.dumps(summary, indent=2))
