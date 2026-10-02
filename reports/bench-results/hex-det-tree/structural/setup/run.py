#!/usr/bin/env python3
"""Bounded manual comparison of integrated structural det against Mathlib.

Proof probes only; no Mathlib-importing executable benchmark is registered.
Quiet measurements and route/axiom audits use separate fresh modules.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease, AXIOMS
from scripts.bench.det_bench_limits import supervise

PROBES = ROOT / 'bench/HexPolyDetMathlib/ProofProbe'
PREFIX = 'HexPolyDetMathlib.ProofProbe'
CASES = [
    ('Diagonal2', 'triangular', 'small'),
    ('Rational2', 'small', 'small'),
    ('Triangular3', 'triangular', 'small'),
    ('Independent5', 'sparse-cofactor', 'small'),
    ('RationalFive3', 'rational-row-factor', 'small'),
    ('RationalOne', 'rational-row-factor', 'one-second'),
    ('SparseOne', 'sparse-cofactor', 'one-second'),
    ('RationalTen', 'rational-row-factor', 'ten-second'),
    ('SparseTen', 'sparse-cofactor', 'ten-second'),
]
ROUTES = {
    'triangular': 'HexPolyDetMathlib.Structural.triangular',
    'small': 'Matrix.det_fin_two_of',
    'sparse-cofactor': 'HexPolyDetMathlib.Structural.cofactor',
    'rational-row-factor': 'HexPolyDetMathlib.RatFactor.det',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cases', nargs='+', choices=[c[0] for c in CASES])
    args = parser.parse_args()
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=False)
    cases = [c for c in CASES if args.cases is None or c[0] in args.cases]
    (root/'StructuralBaseline.lean.txt').write_text((PROBES/'StructuralBaseline.lean').read_text())
    (root/'run.py').write_text(Path(__file__).read_text())
    records = []
    plan = dict(cases=cases, pairs=6, build_cap_seconds=60,
                total_cap_seconds=1800, stop_on_confirmed_loss=True,
                loss_rule='Mathlib wins >=5/6 whole-build deltas and median advantage >200 ms',
                unchanged_reruns=0)
    (root/'plan.json').write_text(json.dumps(plan, indent=2))

    def run(deadline):
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
        os.environ['LEAN_NUM_THREADS'] = '1'
        topology = sweep.cpu_topology(cpu)
        monitored = sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
        environment = sweep.environment()

        def save():
            (root/'results.json').write_text(json.dumps(dict(plan=plan, cpu=cpu,
                topology=topology, environment=environment, cases=records), indent=2))

        def observe(module, result):
            with (root/'observations.jsonl').open('a') as f:
                f.write(json.dumps(dict(module=module, result=result))+'\n')

        def build(module):
            seconds = min(60, deadline-time.monotonic()-2)
            if seconds <= 0:
                raise RuntimeError('total measurement deadline exhausted')
            return sweep.build_sample(module, seconds, cpu, monitored, observe, True)

        baseline = PREFIX+'.StructuralBaseline'
        try:
            for name, route, stage in cases:
                record = dict(name=name, route=route, stage=stage, state='audit', samples=[], audits={})
                records.append(record)
                save()
                for arm in ['Hex', 'Mathlib']:
                    module = PREFIX+'.Structural'+name+arm
                    source = PROBES/('Structural'+name+arm+'.lean')
                    text = source.read_text()
                    (root/(source.name+'.txt')).write_text(text)
                    record.setdefault('sources', {})[arm] = hashlib.sha256(text.encode()).hexdigest()
                    # Build the same quiet module once to audit it independently of timed pairs.
                    build(module)
                    audit_name = 'StructuralAudit'+name+arm
                    audit = PROBES/(audit_name+'.lean')
                    target = module+'.result'
                    audit_text = f'import {module}\n#print axioms {target}\n'
                    if arm == 'Hex':
                        audit_text += f'''run_meta do
  let root := ``{target}
  let mut pending := [root]
  let mut found := false
  while let name :: rest := pending do
    pending := rest
    let some value := (← Lean.getConstInfo name).value? (allowOpaque := true)
      | throwError "missing determinant proof"
    for used in value.getUsedConstants do
      if used == ``{ROUTES[route]} then found := true
      if root.isPrefixOf used then pending := used :: pending
  unless found do throwError "intended structural route was not used"
'''
                    assert not audit.exists()
                    audit.write_text(audit_text)
                    (root/(audit.name+'.txt')).write_text(audit_text)
                    try:
                        result = build(PREFIX+'.'+audit_name)
                    finally:
                        audit.unlink(missing_ok=True)
                    match = re.search(r"'"+re.escape(target)+r"' depends on axioms: \[(.*?)\]", result['compiler_output'])
                    actual = None if match is None else [a.strip() for a in match[1].split(',')]
                    if actual != list(AXIOMS):
                        raise RuntimeError(f'{name} {arm}: unexpected axioms {actual}')
                    record['audits'][arm] = result
                    save()
                record['state'] = 'measuring'
                save()
                for trial in range(1, 7):
                    for arm in (['Mathlib', 'Hex'] if trial % 2 else ['Hex', 'Mathlib']):
                        module = PREFIX+'.Structural'+name+arm
                        order = [('reference', baseline), ('candidate', module)]
                        if not trial % 2:
                            order.reverse()
                        built = {role: build(mod) for role, mod in order}
                        record['samples'].append(dict(trial=trial, arm=arm,
                            build_order=[r for r, _ in order], **built,
                            delta_ms=(built['candidate']['wall_nanos']-built['reference']['wall_nanos'])/1e6))
                        save()
                    record['medians_ms'] = {arm: statistics.median(s['delta_ms'] for s in record['samples'] if s['arm']==arm) for arm in ['Mathlib', 'Hex']}
                    record['mathlib_wins'] = sum(
                        next(s['delta_ms'] for s in record['samples'] if s['trial']==i and s['arm']=='Mathlib') <
                        next(s['delta_ms'] for s in record['samples'] if s['trial']==i and s['arm']=='Hex')
                        for i in range(1, trial+1))
                    save()
                    print('PAIR', name, trial, json.dumps(record['medians_ms']), flush=True)
                record['state'] = 'complete'
                save()
                med = record['medians_ms']
                if record['mathlib_wins'] >= 5 and med['Hex']-med['Mathlib'] > 200:
                    record['state'] = 'confirmed-loss-stop'
                    save()
                    break
        except BaseException as error:
            if records:
                records[-1]['state'] = 'stopped'
                records[-1]['error'] = str(error)
                save()
            raise
        finally:
            lease.close()
    return supervise(run, 1800, root/'status.json')


if __name__ == '__main__':
    raise SystemExit(main())
