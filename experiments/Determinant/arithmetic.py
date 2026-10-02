#!/usr/bin/env python3
"""Two diagnostic AB/BA pairs of the fixed witness's arithmetic obligations.

First build Determinant.Fixture and Determinant.Arithmetic. Pass the Fixture
build log and a new output directory. Each completed sample, including failed
ones, is retained. One failure aborts the batch: no larger case is scheduled.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep
from scripts.bench.det_symbolic_sweep import cpu_lease
from scripts.bench.det_bench_limits import supervise


def literal(p):
    return '[' + ', '.join(f'({es}, ({c} : Int))' for es, c in p) + ']'


def polynomial(p):
    return '(' + (' + '.join('(' + ' * '.join(
        [f'({c} : Int)'] + [f'(x{i} ^ ({e} : Nat))' for i, e in enumerate(es) if e]) + ')'
        for es, c in p) or '0') + ')'


def source(obligations, arm):
    statements = []
    for left, (right, result) in obligations:
        if arm == 'Replay':
            ls = '[' + ', '.join(map(literal, left)) + ']'
            rs = '[' + ', '.join(map(literal, right)) + ']'
            statements.append(f'Hex.MvPoly.Kernel.beq ((Hex.PolyDet.ops 2).dot {ls} {rs}) {literal(result)} = true')
        else:
            lhs = ' + '.join(f'{polynomial(a)} * {polynomial(b)}' for a, b in zip(left, right))
            statements.append(f'{lhs} = {polynomial(result)}')
    variables = '' if arm == 'Replay' else ' (x0 x1 : Int)'
    tactic = {'Replay': 'decide +kernel', 'Ring': 'plain_ring', 'Cached': 'cached_ring'}[arm]
    return ('import Determinant.Arithmetic\nopen Determinant\n'
            'set_option maxHeartbeats 500000\nset_option maxRecDepth 10000\n'
            'set_option profiler true\nset_option profiler.threshold 1\n'
            f'theorem result{variables} :\n  ' + ' ∧\n  '.join(f'({s})' for s in statements) +
            f' ∧ True := by\n  timed_proof\n    {tactic}\n#print axioms result\n')


def main():
    fixture_log, output = map(Path, sys.argv[1:])
    match = re.search(r'FIXTURE (.*)', fixture_log.read_text())
    if match is None:
        raise SystemExit('No FIXTURE record in log; use an archived fixture log or '
                         'remove .lake/build/lib/lean/Determinant/Fixture.olean '
                         'and rebuild Determinant.Fixture before running this script.')
    obligations = json.loads(match[1])
    output.mkdir(parents=True, exist_ok=False)
    (output / 'fixture.json').write_text(json.dumps(obligations, indent=2) + '\n')
    files = [Path(__file__), ROOT / 'experiments/Determinant/Arithmetic.lean',
             ROOT / 'experiments/Determinant/Fixture.lean', ROOT / 'HexMvPoly/Kernel.lean']
    (output / 'sources.json').write_text(json.dumps({str(p.relative_to(ROOT)):
        hashlib.sha256(p.read_bytes()).hexdigest() for p in files}, indent=2))
    for p in files[:3]:
        (output / (p.name + '.txt')).write_bytes(p.read_bytes())

    def run(deadline):
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
        os.environ['LEAN_NUM_THREADS'] = '1'
        topology = sweep.cpu_topology(cpu)
        monitored = sweep.parse_cpu_list(topology.get('thread_siblings_list')) or [cpu]
        records = []
        environment = sweep.environment()
        def observe(module, result):
            with (output / 'observations.jsonl').open('a') as f:
                f.write(json.dumps(dict(module=module, result=result)) + '\n')
        try:
            # Pair Replay/Ring first, then Ring/Cached to isolate reuse.
            for arms in [('Replay', 'Ring'), ('Ring', 'Cached')]:
                for pair in range(2):
                    for arm in (arms if pair == 0 else arms[::-1]):
                        module = 'Determinant.Sample' + arm
                        path = ROOT / 'experiments' / Path(*module.split('.')).with_suffix('.lean')
                        assert not path.exists(), path
                        code = source(obligations, arm)
                        path.write_text(code)
                        (output / (path.name + '.txt')).write_text(code)
                        try:
                            result = sweep.build_sample(module, min(60, deadline-time.monotonic()-2),
                                cpu, monitored, observe, True)
                        finally:
                            path.unlink(missing_ok=True)
                        text = result['compiler_output']
                        call = int(re.search(r'CALL_NS (\d+)', text)[1]) / 1e6
                        line = code[:code.index('theorem result')].count('\n') + 1
                        checks = re.findall(rf'info: [^\n]+:{line}:8: type checking took ([0-9.e+]+)(ms|s)', text)
                        assert len(checks) <= 1, checks
                        kernel = (float(checks[0][0]) * (1000 if checks[0][1] == 's' else 1)
                                  if checks else None)
                        axiom_line = re.search(r"'result' depends on axioms: \[(.*?)\]", text)
                        assert axiom_line, text
                        axioms = set(axiom_line[1].split(', ')) - {''}
                        assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
                        records.append(dict(comparison=arms, pair=pair, arm=arm, call_ms=call,
                            final_kernel_ms=kernel, proof_lower_ms=call+(kernel or 0),
                            proof_upper_ms=call+(kernel if kernel is not None else 1), result=result))
                        (output / 'results.json').write_text(json.dumps(dict(cpu=cpu,
                            topology=topology, environment=environment, samples=records), indent=2))
                        print(arms, pair, arm, round(call, 2), kernel, flush=True)
        finally:
            lease.close()

    return supervise(run, 240, output / 'status.json')


if __name__ == '__main__':
    raise SystemExit(main())
