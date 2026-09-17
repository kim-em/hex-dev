#!/usr/bin/env python3
"""Preregistered classification, forced-arm comparison, then fixed-table dispatch.

All observations, including failures and expected declines, are retained. Each
proof sample uses the existing fresh-module runner and an adjacent import-only
baseline; six trial-major rounds alternate the two arms. The compiled driver
classifies actual witness products before any timed comparisons.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import AXIOMS, cpu_lease, routes

PREFIX = 'HexPolyDetMathlib.ProofProbe.Packed'
MANIFEST = ROOT / 'scripts/bench/det_packed_manifest.json'


def pairs(case, arms):
    return [sweep.ProbePair(case['stem'] + arm,
        sweep.ProbeModule(f'{PREFIX}{case["stem"]}{arm}Baseline'),
        sweep.ProbeModule(f'{PREFIX}{case["stem"]}{arm}', AXIOMS),
        dict(case, arm=arm)) for arm in arms]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['classify', 'forced', 'dispatch'])
    parser.add_argument('output', type=Path)
    parser.add_argument('--classification', type=Path)
    parser.add_argument('--forced', type=Path)
    parser.add_argument('--case', action='append', help='diagnostic subset only')
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    cases = [c for c in manifest['cases'] if not args.case or c['stem'] in args.case]
    arms = ['Lists', 'Packed'] if args.stage == 'forced' else ['Dispatch', 'Mathlib']
    spec = sweep.SweepSpec(__doc__, tuple(p for c in cases for p in pairs(c, arms)),
        'HexPolyDetMathlibProofProbe', 'hex-det-packed-sweep-v1',
        'paired-fresh-module-olean-wall', 'hex-det-packed', required_samples=6,
        absolute_only=True, extra_sources=(Path('scripts/bench/det_packed_manifest.json'),
        Path('scripts/bench/det_packed_probes.py'), Path('bench/HexPolyDet/PackedBench.lean'),
        *(Path('bench/HexPolyDet/packed-inputs') / (c['stem'] + '.json') for c in cases)))
    sweep.validate_spec(spec)
    if args.stage != 'classify' and not args.classification:
        parser.error('timing requires --classification from the completed preflight')
    classification = json.loads(args.classification.read_text()) if args.classification else None
    if classification and (not classification['schedule_complete'] or classification['subset'] != bool(args.case)):
        parser.error('classification must be complete and cover the same scope')
    if args.stage == 'dispatch':
        if not args.forced:
            parser.error('dispatch requires the completed --forced comparison')
        forced = json.loads(args.forced.read_text())
        if not forced['schedule_complete'] or not forced['sources_unchanged']:
            parser.error('forced comparison must finish with unchanged sources before dispatch')
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    env = sweep.environment()
    hashes = sweep.source_hashes(spec, Path(__file__))
    topology = sweep.cpu_topology(cpu)
    monitored = sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
    records, profiles, classified = [], [], {}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    expected = len(cases) if args.stage == 'classify' else len(cases) * 12

    def save():
        summary = {}
        for c in cases:
            a = {}
            for arm in arms:
                rows = [r for r in records if r['stem'] == c['stem'] and r['arm'] == arm]
                deltas = [r['delta_ns'] for r in rows if r.get('delta_ns') is not None]
                a[arm] = dict(samples=len(rows), completed=len(deltas),
                    median_delta_ns=statistics.median(deltas) if len(deltas) == 6 else None,
                    routes=sorted({e['route'] for r in rows for e in r.get('routes', [])}),
                    artifacts=sweep.artifact_sizes(f'{PREFIX}{c["stem"]}{arm}', Path('bench')))
            summary[c['stem']] = dict(c, arms=a)
        obj = dict(schema=spec.schema, stage=args.stage, manifest=manifest,
            subset=bool(args.case), environment=env, cpu=cpu, topology=topology,
            provenance_issues=sweep.dirty_issues(dict(env['repository']), dict(env['dependency_checkouts'])),
            source_hashes=hashes, sources_unchanged=hashes == sweep.source_hashes(spec, Path(__file__)),
            schedule_complete=(len(classified) if args.stage == 'classify' else len(records)) == expected,
            classification=classified if args.stage == 'classify' else classification['classification'],
            classification_sha256=hashlib.sha256(args.classification.read_bytes()).hexdigest() if args.classification else None,
            forced_sha256=hashlib.sha256(args.forced.read_bytes()).hexdigest() if args.forced else None,
            samples=records, profiles=profiles, summary=summary,
            default_simproc_enabled=False)
        tmp = args.output.with_suffix('.tmp')
        tmp.write_text(json.dumps(obj, indent=2) + '\n')
        tmp.replace(args.output)

    def build(module):
        observed = []
        try:
            result = sweep.build_sample(module.module, 45, cpu, monitored,
                lambda _m, r: observed.append(r), retain_compiler_output=True)
            sweep.validate_axioms(module.module, 'candidate', module, result)
            return dict(result, state='complete')
        except RuntimeError as e:
            result = dict(observed[-1]) if observed else {}
            return dict(result, state=result.get('state', 'failed'), error=str(e))

    if args.stage == 'classify':
        for case in cases:
            stem = case['stem']
            print(f'[classify] {stem}', flush=True)
            if case['dimension'] <= 3:
                classified[stem] = dict(classification='closed-form')
            else:
                try:
                    proc, wall, metrics = sweep.run_timed([
                        str(ROOT / '.lake/build/bin/hex_poly_det_packed'),
                        str(ROOT / 'bench/HexPolyDet/packed-inputs' / (stem + '.json'))], 45)
                    classified[stem] = dict(json.loads(proc.stdout) if proc.returncode == 0 else
                        dict(classification='producer-failure'), wall_nanos=wall,
                        metrics=metrics, stdout=proc.stdout, stderr=proc.stderr)
                except subprocess.TimeoutExpired as e:
                    classified[stem] = dict(classification='producer-timeout', timeout_seconds=45,
                        stdout=str(e.stdout or ''), stderr=str(e.stderr or ''))
            save()
    else:
        sweep.warm_imports(spec, 1200)
        for trial in range(6):
            for case in sweep.rotate(cases, trial):
                adjacent = pairs(case, arms)
                if trial % 2:
                    adjacent.reverse()
                for pair in adjacent:
                    arm = pair.metadata['arm']
                    status = classification['classification'][case['stem']]['classification']
                    print(f'[{trial+1}/6] {case["stem"]} {arm} ({status})', flush=True)
                    if args.stage == 'forced' and arm == 'Packed' and status not in ['eligible', 'closed-form']:
                        records.append(dict(stem=case['stem'], arm=arm, trial=trial+1,
                            state='expected-decline', classification=status, delta_ns=None))
                    else:
                        modules = sweep.ordered_modules(pair, trial)
                        built = {role: build(module) for role, module in modules}
                        valid = all(r['state'] == 'complete' for r in built.values())
                        records.append(dict(stem=case['stem'], arm=arm, trial=trial+1,
                            build_order=[r for r,_ in modules], **built,
                            routes=routes(built['candidate'].get('compiler_output', '')),
                            delta_ns=(built['candidate']['wall_nanos']-built['reference']['wall_nanos']) if valid else None))
                    save()
        if args.stage == 'dispatch':
            for stem in manifest['profile_cases']:
                if any(c['stem'] == stem for c in cases):
                    print(f'[profile] {stem}', flush=True)
                    profiles.append(dict(stem=stem, result=build(sweep.ProbeModule(f'{PREFIX}{stem}Profile', AXIOMS))))
                    save()
        if args.stage == 'forced':
            for case in cases:
                status = classification['classification'][case['stem']]['classification']
                if status not in ['eligible', 'packed-decline']:
                    continue
                print(f'[compiled phases] {case["stem"]}', flush=True)
                try:
                    proc, wall, metrics = sweep.run_timed([str(ROOT / '.lake/build/bin/hex_poly_det_packed'),
                        str(ROOT / 'bench/HexPolyDet/packed-inputs' / (case['stem'] + '.json')), '--time'], 45)
                    profiles.append(dict(stem=case['stem'], compiled=json.loads(proc.stdout) if proc.returncode == 0 else None,
                        wall_nanos=wall, metrics=metrics, stdout=proc.stdout, stderr=proc.stderr))
                except subprocess.TimeoutExpired as e:
                    profiles.append(dict(stem=case['stem'], state='timeout', timeout_seconds=45))
                save()
    save()
    lease.close()

if __name__ == '__main__':
    main()
