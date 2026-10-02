#!/usr/bin/env python3
"""Boundary, singularity and row-pivot differential checks, not timing samples."""
import json
from pathlib import Path
import subprocess
import sys
import time

from runtime import ROOT, oracle
from scripts.bench.det_bench_limits import supervise


def main():
    output = Path(sys.argv[1])
    output.mkdir(parents=True, exist_ok=False)
    (output / 'verify.py.txt').write_bytes(Path(__file__).read_bytes())
    cases = [('int', n, 'dense', 1) for n in [0, 1, 2]]
    cases += [(ring, 5, shape, spread) for ring, spread in
              [('int', 1), ('rat', 1), ('dyadic', 64)] for shape in ['swap', 'singular']]
    cases += [(ring, 0, 'dense', 1) for ring in ['rat', 'dyadic']]
    def run(deadline):
        count = 0
        for ring, n, shape, spread in cases:
            arms = ['bareiss', 'bird', 'berkowitz']
            if ring == 'int':
                arms += ['stages-owned', 'stages-word']
            if ring == 'rat':
                arms += ['scaled']
            if ring == 'dyadic':
                arms = ['bird', 'berkowitz', 'scaled']
            for arm in arms:
                cmd = [str(ROOT / '.lake/build/bin/determinant_experiment'), ring,
                       arm, str(n), '8', shape, str(spread)]
                proc = subprocess.run(cmd, capture_output=True, text=True,
                                      timeout=min(60, deadline-time.monotonic()-2))
                record = dict(command=cmd, exit_status=proc.returncode,
                              stdout=proc.stdout, stderr=proc.stderr)
                with (output / 'observations.jsonl').open('a') as f:
                    f.write(json.dumps(record) + '\n')
                assert proc.returncode == 0, record
                inputs, result = map(json.loads, proc.stdout.splitlines())
                entries = inputs['input']
                if shape == 'swap':
                    nonzero = (lambda q: q != 0) if ring == 'int' else (lambda q: q[0] != 0)
                    assert not nonzero(entries[0][0])
                    assert any(nonzero(row[0]) for row in entries[1:])
                checked = oracle(ring, entries, result['value'])
                assert checked['valid'], (record, checked)
                count += 1
        imports = json.loads((ROOT / '.lake/build/ir/Determinant/Runtime.setup.json').read_text())['importArts']
        assert not any('Mathlib' in name for name in imports), list(imports)
        (output / 'checks.json').write_text(json.dumps(dict(passed=count,
            mathlib_imports=[], imports=sorted(imports)), indent=2))
        print(f'{count} exact differential checks passed; computational import closure is Mathlib-free')
    return supervise(run, 240, output / 'status.json')


if __name__ == '__main__':
    raise SystemExit(main())
