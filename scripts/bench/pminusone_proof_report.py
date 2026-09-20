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


def summarize(paths):
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
                'resolution': result['workload_ratio_resolution']}
        cases[name] = case
        groups[case['family']].append((case, timings))
        if case['all_continuations_miss']:
            groups['miss-construction'].append((case, timings))
    assert set(cases) == EXPECTED, 'incomplete input corpus'
    families = []
    for family, entries in sorted(groups.items()):
        chosen = [(c, t) for c, t in entries if c['checked_disabled'] and c['checked_enabled']
                  and c['opportunity_continuations'] > 0] if family.startswith('opportunity') else entries
        ref = median(v for _, t in chosen for v in t['reference']) if chosen else None
        cand = median(v for _, t in chosen for v in t['candidate']) if chosen else None
        resolved = bool(chosen) and all(c['resolution'] == 'resolved' for c, _ in chosen)
        families.append({'family': family, 'cases': len(entries),
                         'checked_disabled': sum(c['checked_disabled'] for c, _ in entries),
                         'checked_enabled': sum(c['checked_enabled'] for c, _ in entries),
                         'losses': sum(c['loss'] for c, _ in entries),
                         'gains': sum(c['gain'] and c['opportunity_continuations'] > 0 for c, _ in entries),
                         'timing_cases': len(chosen), 'resolved': resolved,
                         'median_disabled_workload_s': ref / 1e9 if ref is not None else None,
                         'median_enabled_workload_s': cand / 1e9 if cand is not None else None,
                         'ratio': cand / ref if ref and ref > 0 and cand > 0 else None})
    retained = not any(c['loss'] for c in cases.values())
    useful = any(f['family'].startswith('opportunity') and (f['gains'] or
                 (f['resolved'] and f['ratio'] is not None and f['ratio'] <= 0.9)) for f in families)
    controls = [f for f in families if f['family'].startswith('miss') or
                f['family'] in ('balanced', 'smooth', 'table')]
    regression = bool(controls) and any(f['family'].startswith('miss') for f in controls) and all(
        f['resolved'] and f['ratio'] is not None and f['ratio'] <= 1.1 for f in controls)
    return {'complete': True, 'sources': sources, 'source_commit': commit,
            'source_sha256': hashes, 'measurement_release_quality': release,
            'fresh_builds': 32 * len(cases), 'checked_disabled': sum(c['checked_disabled'] for c in cases.values()),
            'checked_enabled': sum(c['checked_enabled'] for c in cases.values()),
            'families': families, 'cases': list(cases.values()),
            'retains_all_checked_successes': retained, 'resolved_usefulness': bool(useful),
            'resolved_regression_limits': regression,
            'gate': 'pass' if release and retained and useful and regression else 'not-established',
            'interpretation': 'Construction-search attribution; unresolved timings cannot pass the default-enable gate.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='+', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(summarize(args.files), indent=2) + '\n'
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end='')
