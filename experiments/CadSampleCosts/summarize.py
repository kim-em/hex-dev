#!/usr/bin/env python3
"""Render report tables from the retained observations; never rerun a sample."""
import json
import hashlib
import math
import re
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
NAMES = {
    'nlsat': ('NLSAT', 'Nlsat', '3/16'),
    'circle-parabola': ('Circle/parabola', 'CircleParabola', '4/1'),
    'circles': ('Two circles', 'Circles', '2/4'),
    'kahan': ('Kahan specialization', 'Kahan', '2/2'),
    'sphere': ('Sphere section', 'Sphere', '4/10'),
    'tower4': ('Tower 4', 'Tower4', '4/2'),
    'tower8': ('Tower 8', 'Tower8', '8/2'),
    'circle-parabola-zero': ('Circle/parabola zero', 'Vanishing', '4/1'),
}


def dh(p):
    return f"{p['degree']}/{p['height']}"


def spread(values, digits=3):
    return f'{statistics.median(values):.{digits}f} [{min(values):.{digits}f}, {max(values):.{digits}f}]'


def primitive_key(poly):
    """Primitive positive-leading coefficients of this corpus's univariate factors."""
    terms = re.findall(r'[+-]?[^+-]+', poly.replace(' ', ''))
    coeffs = {}
    for term in terms:
        m = re.fullmatch(r'([+-]?)([0-9]*)(x(?:\^([0-9]+))?)?', term)
        if not m or not (m[2] or m[3]):
            raise ValueError(f'unsupported projected polynomial: {poly}')
        degree = int(m[4] or 1) if m[3] else 0
        coeff = int(m[2] or 1) * (-1 if m[1] == '-' else 1)
        coeffs[degree] = coeffs.get(degree, 0) + coeff
    vector = [coeffs.get(i, 0) for i in range(max(coeffs)+1)]
    while vector and vector[-1] == 0:
        vector.pop()
    divisor = math.gcd(*vector)
    if not divisor:
        raise ValueError('zero is not a projected factor')
    divisor *= -1 if vector[-1] < 0 else 1
    return tuple(c // divisor for c in vector)


def tables(directory):
    rows = [json.loads(line) for line in (directory / 'runs.jsonl').read_text().splitlines()]
    assert len(rows) == 99
    for row in rows:
        assert row['exit_code'] == 0 and not row['timed_out'], row['log']
        assert not any('error' in key for key in row) and not row.get('invalid_axioms'), row['log']
        assert (directory / row['log']).is_file(), row['log']
    lift = ['| Example | Level | Input/coefficient d/H | Root d/H | Substitution ms | Root enumeration ms |',
            '|---|---:|---|---|---:|---:|']
    for example, (name, _, _) in NAMES.items():
        runs = [r for r in rows if r['kind'] == 'runtime' and r['example'] == example]
        if not runs:
            continue
        assert len(runs) == 4
        for stage in runs[0]['stages']:
            if stage.get('operation') not in ('ZPoly.realAlgebraicRoots', 'RealAlgebraicPoly.roots'):
                continue
            level, operation = stage['level'], stage['operation']
            stages = [s for r in runs for s in r['stages']
                      if s.get('level') == level and s.get('operation') == operation]
            # A stable shape is required to summarize four timings with one d/H.
            assert all(s['input'] == stage['input'] and s['roots'] == stage['roots'] for s in stages)
            inp = stage['input'] if level == 1 else stage['input'][0]
            roots = ', '.join(dict.fromkeys(dh(p) for p in stage['roots']))
            sub = [s['ns'] / 1e6 for r in runs for s in r['stages']
                   if s.get('level') == level and s.get('operation') == 'substitution']
            lift.append(f'| {name} | {level} | {dh(inp)} | {roots} | '
                        f'{spread(sub) if sub else "—"} | {spread([s["ns"] / 1e6 for s in stages])} |')
    snapshot = directory / 'kernel-inputs.json'
    recorded = json.loads((directory / 'meta.json').read_text())
    assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == recorded['sources']['experiments/CadSampleCosts/kernel-inputs.json']
    meta = json.loads(snapshot.read_text())
    kernel = ['| Example (level 2 sign) | Parameter d/H | Carrier d/H | Chain bits | Literal s | Replay s | Paired difference s |',
              '|---|---|---|---:|---:|---:|---:|']
    for example, (name, module, parameter) in NAMES.items():
        runs = [r for r in rows if r['kind'] == 'proof' and r['example'] == example]
        assert len(runs) == 8
        a = {r['round']: r['wall_ns'] / 1e9 for r in runs if r['arm'] == 'Literal'}
        b = {r['round']: r['wall_ns'] / 1e9 for r in runs if r['arm'] == 'Replay'}
        assert set(a) == set(b) == set(range(4))
        m = meta[module]
        kernel.append(f'| {name} | {parameter} | {m["carrier_degree"]}/{m["carrier_height"]} | '
                      f'{m["sturm_max_height"].bit_length()} | {statistics.median(a.values()):.2f} | '
                      f'{statistics.median(b.values()):.2f} | {spread([b[i] - a[i] for i in range(4)], 2)} |')
    inputs = {'nlsat': '3/5', 'circle-parabola': '2/1', 'circles': '2/2',
              'kahan': '2/64', 'sphere': '2/6', 'tower4': '2/2', 'tower8': '4/2'}
    assert set(inputs) == {r['example'] for r in rows if r['kind'] == 'solver'}
    solver = ['| Example | Levels | Input d/H | Result | Cell explanations | Primitive projected factors per explanation, in order | Learned clauses | Invocation ms |',
              '|---|---:|---|---|---:|---|---:|---:|']
    for r in rows:
        if r['kind'] != 'solver':
            continue
        example = r['example']
        counts = ', '.join(str(len({primitive_key(p) for p in e['projection_factors']})) for e in r['explanations']) or '—'
        solver.append(f'| {NAMES[example][0]} | {3 if example == "sphere" else 2} | {inputs[example]} | '
                      f'{", ".join(r["result"])} | {len(r["explanations"])} | {counts} | '
                      f'{len(r["learned_clauses"])} | {r["wall_ns"] / 1e6:.3f} |')
    return {'LIFT_TABLE': '\n'.join(lift), 'KERNEL_TABLE': '\n'.join(kernel), 'SOLVER_TABLE': '\n'.join(solver)}


def focused_table(directory):
    rows = [json.loads(line) for line in (directory / 'runs.jsonl').read_text().splitlines()]
    assert len(rows) == 32
    recorded = json.loads((directory / 'meta.json').read_text())
    snapshot = directory / 'kernel-inputs.json'
    assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == recorded['sources']['experiments/CadSampleCosts/kernel-inputs.json']
    meta = json.loads(snapshot.read_text())
    lines = ['| Example (level 2 sign) | Parameter d/H | Carrier d/H | Chain bits | Kernel type checking ms | Command heartbeats |',
             '|---|---|---|---:|---:|---:|']
    for example, (name, module, parameter) in NAMES.items():
        runs = [r for r in rows if r['example'] == example]
        assert len(runs) == 4 and {r['round'] for r in runs} == set(range(4))
        for row in runs:
            assert row['exit_code'] == 0 and not row['timed_out'] and 'parse_error' not in row
            assert (directory / row['log']).is_file()
        beats = {r['heartbeats'] for r in runs}
        assert len(beats) == 1
        m = meta[module]
        lines.append(f'| {name} | {parameter} | {m["carrier_degree"]}/{m["carrier_height"]} | '
                     f'{m["sturm_max_height"].bit_length()} | {spread([r["kernel_ms"] for r in runs], 1)} | {beats.pop()} |')
    return '\n'.join(lines)


if __name__ == '__main__':
    for label, table in tables(Path(sys.argv[1])).items():
        print(f'<!-- {label} -->\n{table}\n')
    if len(sys.argv) > 2:
        print(focused_table(Path(sys.argv[2])))
