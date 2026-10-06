# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison
"""Check a complete retained capture against the declared median comparison.

No benchmarks are run. This applies the arithmetic of pinned lean-bench's
baseline comparison to three native child observations per arm and parameter.
These child outputs do not contain runner signal-floor/verdict eligibility;
this is not a replay of the full runner's eligibility machinery.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import statistics

THRESHOLD_PERCENT = 10.0
POLICY = "lean-bench 8a37daf1074c3bdbd0da479b55538bad4a0022db: LeanBench/Export.lean perCallAtParam/classifyChange/compareParametric (default 10.0)"


def analyze(root):
    schedule = json.loads((root / 'schedule.json').read_text())
    context = json.loads((root / 'context.json').read_text())
    sources = json.loads((root / 'sources.json').read_text())
    if schedule['trials'] != 3:
        raise ValueError('expected the declared three-trial comparison')
    if 'finished_unix' not in context:
        raise ValueError('capture has not finished')
    if hashlib.sha256((root / 'measure.py').read_bytes()).hexdigest() != context['script_sha256']:
        raise ValueError('measurement script differs from the capture context')
    for arm in ('baseline', 'candidate'):
        if context['binaries_after'][arm] != sources[arm]['binary_sha256']:
            raise ValueError(f'frozen executable changed: {arm}')
    rows = [json.loads(line) for line in (root / 'observations.jsonl').read_text().splitlines()]
    expected = [(trial, w['name'], p, arm)
                for trial in range(3) for w in schedule['workloads']
                for p in w['parameters']
                for arm in (['baseline', 'candidate'] if trial % 2 == 0 else ['candidate', 'baseline'])]
    if [(r['trial'], r['name'], r['param'], r['arm']) for r in rows] != expected:
        raise ValueError('capture does not match the complete ordered schedule')
    groups = {}
    failures = []
    for row in rows:
        stem = f"{row['trial']}-{row['name'].rsplit('.', 1)[-1]}-{row['param']}-{row['arm']}"
        stdout = (root / (stem + '.stdout')).read_text()
        (root / (stem + '.stderr')).read_bytes()
        try:
            raw = json.loads(stdout)
        except ValueError:
            raw = None
        if raw != row.get('observation'):
            raise ValueError(f'raw stdout differs: {stem}')
        if row['returncode'] != 0 or not isinstance(raw, dict) or raw.get('status') != 'ok':
            failures.append(stem)
            continue
        if raw['function'] != row['name'] or raw['param'] != row['param'] or raw['cache_mode'] != 'warm':
            raise ValueError(f'child identity differs: {stem}')
        t = raw['per_call_nanos']
        if not isinstance(t, (int, float)) or not math.isfinite(t) or t <= 0:
            raise ValueError(f'nonpositive or nonfinite observation: {stem}')
        groups.setdefault((row['name'], row['param']), {}).setdefault(row['arm'], []).append(raw)
    if context['failed_arms'] != len(failures):
        raise ValueError('context and observations disagree on failures')
    points = []
    if not failures:
        for (name, param), arms in sorted(groups.items()):
            b = [r['per_call_nanos'] for r in arms['baseline']]
            c = [r['per_call_nanos'] for r in arms['candidate']]
            bm, cm = statistics.median(b), statistics.median(c)
            pct = (cm - bm) / bm * 100.0
            points.append(dict(name=name, param=param, baseline_nanos=b, candidate_nanos=c,
                baseline_median_nanos=bm, candidate_median_nanos=cm, change_percent=pct,
                classification='regression' if pct > THRESHOLD_PERCENT else 'improvement' if pct < -THRESHOLD_PERCENT else 'stable',
                adjacent_ratios=[cv / bv for bv, cv in zip(b, c)],
                median_adjacent_ratio=statistics.median(cv / bv for bv, cv in zip(b, c)),
                hashes_agree=all(br['result_hash'] == cr['result_hash'] for br, cr in zip(arms['baseline'], arms['candidate']))))
    return dict(policy=POLICY, threshold_percent=THRESHOLD_PERCENT, completed_arms=len(rows),
        failures=failures, parameters_compared=len(points),
        regression_count=sum(p['classification'] == 'regression' for p in points),
        improvement_count=sum(p['classification'] == 'improvement' for p in points),
        all_hashes_agree=all(p['hashes_agree'] for p in points) if points else None,
        points=points,
        scope='Arithmetic comparison of all scheduled native observations; not runner signal-floor eligibility, causal attribution, semantic conformance, fresh scaling evidence, or full Phase-6 acceptance.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = analyze(args.capture)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('completed_arms', 'failures', 'parameters_compared', 'regression_count', 'improvement_count', 'all_hashes_agree')}))
    for p in result['points']:
        if p['classification'] == 'regression':
            print(f"{p['name']}@{p['param']}: +{p['change_percent']:.6f}%")
    raise SystemExit(2 if result['failures'] or result['regression_count'] or not result['all_hashes_agree'] else 0)


if __name__ == '__main__':
    main()
