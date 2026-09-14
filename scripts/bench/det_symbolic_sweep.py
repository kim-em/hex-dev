#!/usr/bin/env python3
"""Six trial-major fresh-module samples of every symbolic determinant probe.

Uses fresh_module_sweep's module cleanup, timed Lake builds, host observations,
axiom audit, artifact accounting and alternating pair order. Failure/timeout
observations are retained, and the fixed schedule continues to the next arm.
Every paired arm has its own immediately adjacent import-only baseline.
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_probes import PREFIX

AXIOMS = ('propext', 'Classical.choice', 'Quot.sound')
MANIFEST = ROOT / 'scripts/bench/det_symbolic_manifest.json'


def cpu_lease():
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return cpu, lease
        except BlockingIOError:
            lease.close()
    raise RuntimeError('all measurement CPU leases are held')


def pairs(case):
    baseline = 'AlgebraicBaseline' if case['family'].startswith('closed-algebraic') else 'Baseline'
    return [sweep.ProbePair(
        case['stem'] + arm,
        sweep.ProbeModule(f'{PREFIX}.{arm}{baseline}'),
        sweep.ProbeModule(f'{PREFIX}.{case["stem"]}{arm}', AXIOMS),
        dict(case, arm=arm, fresh_module_budget_ms=case['proof_build_ceiling_ms']))
        for arm in ['Mathlib', 'Hex']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--case', action='append', help='diagnostic subset; never a shipping report')
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    cases = [c for c in manifest['cases'] if not args.case or c['stem'] in args.case]
    probe_pairs = tuple(p for c in cases for p in pairs(c))
    spec = sweep.SweepSpec(__doc__, probe_pairs, 'HexPolyDetMathlibProofProbe',
                           'hex-symbolic-det-sweep-v1', 'paired-fresh-module-olean-wall',
                           'hex-symbolic-det', required_samples=6, absolute_only=True,
                           extra_sources=(Path('scripts/bench/det_symbolic_manifest.json'),
                                          Path('scripts/bench/det_symbolic_probes.py'),
                                          *(Path('bench/HexPolyDetMathlib/ProofProbe') / f'{s}Profile.lean'
                                            for s in manifest['profile_cases'])))
    sweep.validate_spec(spec)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    env = sweep.environment()
    source_hashes = sweep.source_hashes(spec, Path(__file__))
    provenance_issues = sweep.dirty_issues(dict(env['repository']), dict(env['dependency_checkouts']))
    sweep.warm_imports(spec, 1200)
    records, profiles = [], []
    topology = sweep.cpu_topology(cpu)
    monitored = sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
    output = args.output
    output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        summary = {}
        for case in cases:
            stem = case['stem']
            arms = {}
            for arm in ['Mathlib', 'Hex']:
                rows = [r for r in records if r['stem'] == stem and r['arm'] == arm]
                completed = [r for r in rows if r.get('delta_ns') is not None]
                deltas = [r['delta_ns'] for r in completed]
                arms[arm] = dict(samples=len(rows), completed=len(completed),
                    median_delta_ns=statistics.median(deltas) if len(deltas) == 6 else None,
                    artifacts=sweep.artifact_sizes(f'{PREFIX}.{stem}{arm}', Path('bench')))
            a, b = arms['Mathlib']['median_delta_ns'], arms['Hex']['median_delta_ns']
            summary[stem] = dict(case, arms=arms,
                ratio_mathlib_over_hex=a / b if a is not None and b is not None and b > 0 else None,
                hex_faster=(a is not None and b is not None and 0 < b < a))
        unchanged = sweep.source_hashes(spec, Path(__file__)) == source_hashes
        complete = len(records) == len(cases) * 12 and all(
            r.get('delta_ns') is not None for r in records)
        record = dict(schema=spec.schema, manifest=manifest, environment=env,
                      cpu=cpu, topology=topology, source_hashes=source_hashes,
                      sources_unchanged=unchanged, measurement_complete=complete,
                      schedule_complete=len(records) == len(cases) * 12,
                      provenance_issues=provenance_issues,
                      subset=bool(args.case), samples=records, profiles=profiles, summary=summary,
                      shipping_bar_met=(complete and unchanged and not args.case and
                                        all(s['hex_faster'] for s in summary.values() if not s.get('scope_probe'))))
        output.write_text(json.dumps(record, indent=2) + '\n')

    def build(module, timeout):
        observed = []
        try:
            result = sweep.build_sample(module.module, timeout, cpu, monitored,
                lambda _m, r: observed.append(r), retain_compiler_output=True)
            sweep.validate_axioms(module.module, 'candidate', module, result)
            return dict(result, state='complete')
        except RuntimeError as e:
            result = dict(observed[-1]) if observed else {}
            return dict(result, state=result.get('state', 'failed'), error=str(e))

    for trial in range(6):
        for case in sweep.rotate(cases, trial):
            adjacent = pairs(case)
            if trial % 2:
                adjacent.reverse()
            for pair in adjacent:
                arm = pair.metadata['arm']
                print(f'[{trial + 1}/6] {case["stem"]} {arm}', flush=True)
                modules = sweep.ordered_modules(pair, trial)
                built = {role: build(module, case['cleanup_timeout_seconds']) for role, module in modules}
                valid = all(r['state'] == 'complete' for r in built.values())
                records.append(dict(stem=case['stem'], arm=arm, trial=trial + 1,
                    build_order=[r for r, _ in modules], **built,
                    delta_ns=(built['candidate']['wall_nanos'] - built['reference']['wall_nanos']) if valid else None))
                save()
    for stem in manifest['profile_cases']:
        if not any(c['stem'] == stem for c in cases):
            continue
        print(f'[profile] {stem}', flush=True)
        p = sweep.ProbeModule(f'{PREFIX}.{stem}Profile', AXIOMS)
        profiles.append(dict(stem=stem, result=build(p, 45)))
        save()
    save()
    # Keep the lease alive until every sample and its durable record are complete.
    lease.close()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
