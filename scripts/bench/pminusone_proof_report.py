#!/usr/bin/env python3
"""Audit per-input construction probes and matched import-subtracted costs."""
import argparse
from collections import defaultdict
import gzip
import hashlib
import json
from pathlib import Path
import re
from statistics import median
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from pminusone_policy_report import category, continuation

EXPECTED = set(re.findall(r'\("([\w-]+)", \d+\)',
    (ROOT / 'bench/HexPrimality/ProofProbe/PMinusOne/Support.lean').read_text()))
assert len(EXPECTED) == 60


def summarize(paths, budget_record=None):
    sources, cases = [], {}
    hashes, commit = {}, None
    release = True
    fixtures = [json.loads(line) for line in
        (ROOT / 'conformance-fixtures/HexPrimality/pminusone-stage2.jsonl').read_text().splitlines()]
    subjects = {(r['bits'], r['q']): r['n'] for r in fixtures if r['family'] == 'primitive'}
    groups = defaultdict(list)
    for path in paths:
        raw = path.read_bytes()
        data = gzip.decompress(raw) if path.suffix == '.gz' else raw
        record = json.loads(data)
        sources.append({'path': str(path), 'sha256': hashlib.sha256(data).hexdigest()})
        assert record['measurement_state'] == 'complete', 'incomplete collection'
        assert record['config']['samples'] == 8
        assert record['config']['import_baseline_control'] == 'imports'
        current = record['environment']['git_commit']
        if commit is None:
            commit = current
        assert commit == current, 'mixed source commits'
        for name, digest in record['source_sha256'].items():
            assert name not in hashes or hashes[name] == digest, 'mixed source hashes'
            hashes[name] = digest
        release &= record['validity']['release_quality']
        results = record['results']
        names = set(results) - {'imports'}
        assert len(names) == 1 and 'imports' in results
        name = names.pop()
        assert name in EXPECTED and name not in cases, 'unknown or duplicate input'
        result = results[name]
        samples = result['samples']
        assert {sample['round'] for sample in samples} == set(range(1, 9))
        assert len(samples) == len(results['imports']['samples']) == 8
        outcomes = {}
        for sample in samples:
            assert sample['build_order'] == (['reference', 'candidate'] if sample['round'] % 2
                                              else ['candidate', 'reference'])
            for role, enabled in [('reference', False), ('candidate', True)]:
                rows = [json.loads('{"case":' + line.partition('{"case":')[2])
                        for line in sample[role]['compiler_output'].splitlines()
                        if '{"case":' in line]
                assert len(rows) == 1 and rows[0]['case'] == name
                assert rows[0]['enabled'] == enabled
                value = rows[0]['result']
                if enabled in outcomes:
                    assert outcomes[enabled] == value, f'nondeterministic result: {name}'
                outcomes[enabled] = value
                assert sample[f'{role}_workload_wall_nanos'] == (
                    sample[role]['wall_nanos'] - sample['import_baseline_wall_nanos'])
        ref, cand = outcomes[False], outcomes[True]
        events = [e for e in cand['events'] if continuation(e)]
        target_events = []
        if name.startswith('parent-'):
            _, bits, q = name.split('-')
            target_events = [e for e in events if e.get('subject') == subjects[(int(bits), int(q))]]
        timings = {role: [s[f'{role}_workload_wall_nanos'] for s in samples]
                   for role in ('reference', 'candidate')}
        case = {'case': name, 'family': category(name),
                'checked_disabled': ref['checked'], 'checked_enabled': cand['checked'],
                'attempts_disabled': ref['attempts'], 'attempts_enabled': cand['attempts'],
                'continuations': len(events), 'opportunity_continuations': len(target_events),
                'loss': ref['checked'] and not cand['checked'],
                'gain': cand['checked'] and not ref['checked'],
                'all_continuations_miss': bool(events) and all(e['outcome'] == 'noFactor' for e in events),
                'median_disabled_workload_s': median(timings['reference']) / 1e9,
                'median_enabled_workload_s': median(timings['candidate']) / 1e9,
                'resolution': result['workload_ratio_resolution'],
                'baseline_envelope_s': result['import_baseline_robust_envelope_nanos'] / 1e9}
        cases[name] = case
        groups[case['family']].append((case, timings))
        if case['all_continuations_miss']:
            groups['miss-construction'].append((case, timings))
    assert set(cases) == EXPECTED, 'incomplete input corpus'
    families = []
    for family, entries in sorted(groups.items()):
        chosen = [(c, t) for c, t in entries if c['checked_disabled'] and c['checked_enabled']
                  and c['opportunity_continuations'] > 0] if family.startswith('opportunity') else entries
        # A family traversal executes every chosen input once. Preserve that
        # cost by summing each round, not by pooling heterogeneous input times.
        totals = {role: [sum(t[role][i] for _, t in chosen) for i in range(8)]
                  for role in ('reference', 'candidate')}
        ref = median(totals['reference']) if chosen else None
        cand = median(totals['candidate']) if chosen else None
        envelope = sum(c['baseline_envelope_s'] for c, _ in chosen) * 1e9
        baseline_resolved = bool(chosen) and min(ref, cand) > envelope
        families.append({'family': family, 'cases': len(entries),
                         'checked_disabled': sum(c['checked_disabled'] for c, _ in entries),
                         'checked_enabled': sum(c['checked_enabled'] for c, _ in entries),
                         'losses': sum(c['loss'] for c, _ in entries),
                         'gains': sum(c['gain'] and c['opportunity_continuations'] > 0 for c, _ in entries),
                         'timing_cases': len(chosen), 'baseline_resolved': baseline_resolved,
                         'summed_baseline_envelope_s': envelope / 1e9,
                         'disabled_round_workload_s': [v / 1e9 for v in totals['reference']],
                         'enabled_round_workload_s': [v / 1e9 for v in totals['candidate']],
                         'median_disabled_workload_s': ref / 1e9 if ref is not None else None,
                         'median_enabled_workload_s': cand / 1e9 if cand is not None else None,
                         'ratio': cand / ref if baseline_resolved else None})
    retained = not any(c['loss'] for c in cases.values())
    assert budget_record is not None, 'explicit construction budget record required'
    budget = budget_record['budget']
    assert all(key in budget for key in ('maxBits', 'maxFactors', 'maxAttempts', 'definition'))
    required_sources = {'HexPrimality/Construction.lean', 'HexPrimality/Search.lean',
                        'bench/HexPrimality/PMinusOneMeasure.lean'}
    assert required_sources <= set(budget_record['source_sha256'])
    for name, digest in budget_record['source_sha256'].items():
        assert hashes.get(name) == digest, f'budget source mismatch: {name}'
    return {'complete': True, 'sources': sources, 'source_commit': commit,
            'source_sha256': hashes, 'construction_budget': budget_record,
            'measurement_release_quality': release,
            'fresh_builds': 32 * len(cases), 'checked_disabled': sum(c['checked_disabled'] for c in cases.values()),
            'checked_enabled': sum(c['checked_enabled'] for c in cases.values()),
            'families': families, 'cases': list(cases.values()),
            'retains_all_checked_successes': retained,
            'interpretation': 'Descriptive construction-search attribution. Family costs sum inputs within each round; baseline-limited costs have no ratio. Baseline resolution is not evidence of a statistically resolved policy difference. Native per-input timings supply the compiled performance gate.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='+', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--budget', required=True, type=Path)
    args = parser.parse_args()
    result = json.dumps(summarize(args.files, json.loads(args.budget.read_text())), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end='')
