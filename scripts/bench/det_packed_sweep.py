#!/usr/bin/env python3
"""Preregistered classification, forced-arm comparison, then fixed-table dispatch.

All observations, including failures and expected declines, are retained. Each
proof sample uses the existing fresh-module runner and an adjacent import-only
baseline; six trial-major rounds alternate the two arms. The compiled driver
classifies witness products before any timed comparisons; an untimed forced
frontend build then records the actual tree or list product bounds. A shared
ledger limits all stages to one hour; same-arm timeouts prune repeated and
coordinatewise larger cases. Explicit skips never contribute timing evidence.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import AXIOMS, cpu_lease, routes
from scripts.bench.det_packed_report import audit_dispatch
from scripts.bench.det_packed_table import selected_tables
from scripts.bench.det_bench_limits import TimeoutFrontier, reserve, supervise, STAGE_SECONDS

PREFIX = 'HexPolyDetMathlib.ProofProbe.Packed'
MANIFEST = ROOT / 'scripts/bench/det_packed_manifest.json'
LIST_TABLE = Path('reports/bench-results/hex-det-packed/crossover.json')


def read_record(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def pairs(case, arms):
    return [sweep.ProbePair(case['stem'] + arm,
        sweep.ProbeModule(f'{PREFIX}{case["stem"]}{arm}Baseline'),
        sweep.ProbeModule(f'{PREFIX}{case["stem"]}{arm}', AXIOMS),
        dict(case, arm=arm, fresh_module_budget_ms=45000)) for arm in arms]


def main(deadline=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['classify', 'forced', 'dispatch'])
    parser.add_argument('output', type=Path)
    parser.add_argument('--classification', type=Path)
    parser.add_argument('--forced', type=Path)
    parser.add_argument('--budget-ledger', type=Path, help='shared across all three stages; default: output directory/det-budget.json')
    parser.add_argument('--case', action='append', help='diagnostic subset only')
    args = parser.parse_args()
    if deadline is None:
        ledger = args.budget_ledger or args.output.parent / 'det-budget.json'
        seconds = reserve(ledger, args.stage)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        code = supervise(main, seconds, args.output.with_suffix('.status.json'))
        raise SystemExit(code)
    frontier = TimeoutFrontier()
    def remaining():
        # Leave time to save explicit skipped rows before the hard supervisor deadline.
        return max(0, deadline - time.monotonic() - 10)
    def blocker(case, arm):
        if remaining() == 0:
            return dict(state='skipped-budget', reason='determinant workflow wall-time budget')
        return frontier.blocker(case, arm)
    manifest = json.loads(MANIFEST.read_text())
    retained = json.loads((ROOT / LIST_TABLE).read_text())
    list_provenance = dict(path=str(LIST_TABLE), sha256=hashlib.sha256((ROOT / LIST_TABLE).read_bytes()).hexdigest())
    cases = [c for c in manifest['cases'] if not args.case or c['stem'] in args.case]
    arms = ['Lists', 'Packed'] if args.stage == 'forced' else ['Dispatch', 'Mathlib']
    spec = sweep.SweepSpec(__doc__, tuple(p for c in cases for p in pairs(c, arms)),
        'HexPolyDetMathlibProofProbe', 'hex-det-packed-sweep-v1',
        'paired-fresh-module-olean-wall', 'hex-det-packed', required_samples=6,
        absolute_only=True, extra_sources=(LIST_TABLE, Path('scripts/bench/det_packed_manifest.json'),
        Path('scripts/bench/det_packed_probes.py'), Path('scripts/bench/det_packed_table.py'),
        Path('scripts/bench/det_packed_report.py'), Path('scripts/bench/det_bench_limits.py'),
        Path('bench/HexPolyDet/PackedBench.lean'),
        *(Path('bench/HexPolyDetMathlib/ProofProbe') / f'Packed{s}Profile.lean' for s in manifest['profiles'].values()),
        *(Path('bench/HexPolyDet/packed-inputs') / (c['stem'] + '.json') for c in cases)))
    sweep.validate_spec(spec)
    if args.stage != 'classify' and not args.classification:
        parser.error('timing requires --classification from the completed preflight')
    classification = read_record(args.classification) if args.classification else None
    if classification and (not classification['schedule_complete'] or classification['subset'] != bool(args.case)):
        parser.error('classification must be complete and cover the same scope')
    if args.stage == 'dispatch':
        if not args.forced:
            parser.error('dispatch requires the completed --forced comparison')
        forced = read_record(args.forced)
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
    finished = False
    args.output.parent.mkdir(parents=True, exist_ok=True)
    expected = len(cases) if args.stage == 'classify' else len(cases) * 12

    # Carry timeout evidence forward only for the same arm; producer and packed
    # classification timeouts must not censor the Mathlib comparator.
    for prior in [classification, forced if args.stage == 'dispatch' else None]:
        if prior:
            for failure in prior.get('timeout_frontier', []):
                frontier.observe(failure['case'], failure['arm'], 'timeout')

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
            schedule_complete=finished and (len(classified) if args.stage == 'classify' else len(records)) == expected,
            classification=classified if args.stage == 'classify' else classification['classification'],
            classification_sha256=hashlib.sha256(args.classification.read_bytes()).hexdigest() if args.classification else None,
            forced_sha256=hashlib.sha256(args.forced.read_bytes()).hexdigest() if args.forced else None,
            samples=records, profiles=profiles, summary=summary,
            retained_list_keys=retained['keys'], list_table_provenance=list_provenance,
            default_simproc_enabled=False, timeout_frontier=frontier.failures,
            resource_policy=dict(workflow_seconds=3600, stage_seconds=STAGE_SECONDS[args.stage],
                budget_ledger=str(args.budget_ledger or args.output.parent / 'det-budget.json'),
                timeout_pruning='same arm/family/carrier, coordinatewise dimension/atoms/degree/support',
                skipped_rows_are_measurements=False))
        tmp = args.output.with_suffix('.tmp')
        tmp.write_text(json.dumps(obj, indent=2) + '\n')
        tmp.replace(args.output)

    def build(module):
        if remaining() == 0:
            return dict(state='skipped-budget')
        observed = []
        result = {}
        timeout = min(45, remaining())
        try:
            result = sweep.build_sample(module.module, timeout, cpu, monitored,
                lambda _m, r: observed.append(r), retain_compiler_output=True)
            sweep.validate_axioms(module.module, 'candidate', module, result)
            return dict(result, state='complete')
        except RuntimeError as e:
            result = dict(observed[-1]) if observed else dict(result)
            state = result.get('state', 'failed')
            if state == 'timeout' and timeout < 45:
                state = 'skipped-budget'
            return dict(result, state=state, error=str(e))

    if args.stage == 'classify':
        if remaining() > 0:
            sweep.warm_imports(spec, min(1200, remaining()))
        for case in cases:
            stem = case['stem']
            print(f'[classify] {stem}', flush=True)
            blocked = blocker(case, 'Producer') or blocker(case, 'Packed')
            if blocked:
                classified[stem] = dict(classification=blocked['state'], **blocked)
            elif case['dimension'] <= 3:
                classified[stem] = dict(classification='closed-form')
            else:
                timeout = min(45, remaining())
                try:
                    proc, wall, metrics = sweep.run_timed([
                        str(ROOT / '.lake/build/bin/hex_poly_det_packed'),
                        str(ROOT / 'bench/HexPolyDet/packed-inputs' / (stem + '.json'))], timeout)
                    classified[stem] = dict(json.loads(proc.stdout) if proc.returncode == 0 else
                        dict(classification='producer-failure'), wall_nanos=wall,
                        metrics=metrics, stdout=proc.stdout, stderr=proc.stderr)
                except subprocess.TimeoutExpired as e:
                    exhausted = timeout < 45
                    if not exhausted:
                        frontier.observe(case, 'Producer', 'timeout')
                    classified[stem] = dict(classification='skipped-budget' if exhausted else 'producer-timeout', timeout_seconds=timeout,
                        stdout=str(e.stdout or ''), stderr=str(e.stderr or ''))
            native = classified[stem]
            if native['classification'] in ['eligible', 'packed-decline']:
                # Tree bounds include syntax and the target, which canonical-list
                # fixtures cannot recover. Classify the exact frontend route too.
                frontend = build(sweep.ProbeModule(f'{PREFIX}{stem}Packed', AXIOMS))
                frontier.observe(case, 'Packed', frontend['state'])
                events = routes(frontend.get('compiler_output', ''))
                certificates = [e for e in events if e['route'].startswith(('packed/', 'term-list'))]
                classified[stem] = dict(native, native=dict(native), frontend=frontend)
                result = classified[stem]
                if frontend['state'] != 'complete':
                    result.update(classification='frontend-failure')
                elif len(certificates) == 1:
                    event = certificates[0]
                    products = [dict(p, key=list(map(int, re.findall(r':= (\d+)', p['key']))))
                                for p in event['products']]
                    result.update(classification='eligible' if event['route'] == 'packed/plain' else 'packed-decline',
                        selection=dict(native['selection'], products=products, route=event['route']),
                        entries=event.get('entries', 'list'))
                elif any(e['route'] == 'fallback' for e in events):
                    result.update(classification='overall-decline', frontend_routes=events)
                else:
                    result.update(classification='frontend-failure', frontend_routes=events)
            if remaining() > 0:
                save()
    else:
        if remaining() > 0:
            sweep.warm_imports(spec, min(1200, remaining()))
        for trial in range(6):
            for case in sweep.rotate(cases, trial):
                adjacent = pairs(case, arms)
                if trial % 2:
                    adjacent.reverse()
                for pair in adjacent:
                    arm = pair.metadata['arm']
                    status = classification['classification'][case['stem']]['classification']
                    print(f'[{trial+1}/6] {case["stem"]} {arm} ({status})', flush=True)
                    blocked = blocker(case, arm)
                    if blocked:
                        records.append(dict(stem=case['stem'], arm=arm, trial=trial+1,
                            **blocked, candidate=dict(blocked), reference=dict(blocked), routes=[], delta_ns=None))
                    elif args.stage == 'forced' and arm == 'Packed' and status not in ['eligible', 'closed-form']:
                        records.append(dict(stem=case['stem'], arm=arm, trial=trial+1,
                            state='expected-decline', classification=status, delta_ns=None))
                    else:
                        modules = sweep.ordered_modules(pair, trial)
                        built = {}
                        for role, module in modules:
                            built[role] = build(module)
                            if built[role]['state'] == 'timeout':
                                frontier.observe(case, arm, 'timeout')
                                break
                        for role, _ in modules:
                            built.setdefault(role, dict(state='skipped-after-timeout'))
                        events = routes(built['candidate'].get('compiler_output', ''))
                        if args.stage == 'forced' and status == 'eligible' and built['candidate']['state'] == 'complete':
                            wanted = 'packed/plain' if arm == 'Packed' else 'term-list'
                            hits = [e for e in events if e['route'] == wanted]
                            error = None
                            if len(hits) != 1:
                                error = f'expected exactly one {wanted} certificate, saw {[e["route"] for e in events]}'
                            elif arm == 'Packed':
                                actual = [list(map(int, re.findall(r':= (\d+)', p['key']))) for p in hits[0]['products']]
                                expected_keys = [p['key'] for p in classification['classification'][case['stem']]['selection']['products']]
                                if actual != expected_keys:
                                    error = f'quoted witness keys differ from compiled preflight: {actual} != {expected_keys}'
                            if error:
                                built['candidate'].update(state='unexpected-route', error=error)
                        valid = all(r['state'] == 'complete' for r in built.values())
                        records.append(dict(stem=case['stem'], arm=arm, trial=trial+1,
                            build_order=[r for r,_ in modules], **built,
                            routes=events,
                            delta_ns=(built['candidate']['wall_nanos']-built['reference']['wall_nanos']) if valid else None))
                    if remaining() > 0:
                        save()
        if args.stage == 'dispatch':
            for stem in manifest['profiles'].values():
                if any(c['stem'] == stem for c in cases):
                    print(f'[profile] {stem}', flush=True)
                    case = next(c for c in cases if c['stem'] == stem)
                    result = blocker(case, 'Dispatch') or build(sweep.ProbeModule(f'{PREFIX}{stem}Profile', AXIOMS))
                    frontier.observe(case, 'Dispatch', result['state'])
                    profiles.append(dict(stem=stem, result=result))
                    if remaining() > 0:
                        save()
        if args.stage == 'forced':
            for case in cases:
                status = classification['classification'][case['stem']]['classification']
                if status not in ['eligible', 'packed-decline']:
                    continue
                blocked = blocker(case, 'Compiled') or blocker(case, 'Producer')
                if blocked:
                    profiles.append(dict(stem=case['stem'], **blocked))
                    continue
                print(f'[compiled phases] {case["stem"]}', flush=True)
                timeout = min(45, remaining())
                try:
                    proc, wall, metrics = sweep.run_timed([str(ROOT / '.lake/build/bin/hex_poly_det_packed'),
                        str(ROOT / 'bench/HexPolyDet/packed-inputs' / (case['stem'] + '.json')), '--time'], timeout)
                    profiles.append(dict(stem=case['stem'], compiled=json.loads(proc.stdout) if proc.returncode == 0 else None,
                        wall_nanos=wall, metrics=metrics, stdout=proc.stdout, stderr=proc.stderr))
                except subprocess.TimeoutExpired as e:
                    if timeout == 45:
                        frontier.observe(case, 'Compiled', 'timeout')
                    profiles.append(dict(stem=case['stem'], state='timeout' if timeout == 45 else 'skipped-budget', timeout_seconds=timeout))
                save()
    if args.stage == 'dispatch':
        _, tables = selected_tables(read_record(args.forced))
        audit_dispatch(dict(samples=records, classification=classification['classification']), dict(keys_by_entries=tables))
    finished = True
    save()
    lease.close()

if __name__ == '__main__':
    main()
