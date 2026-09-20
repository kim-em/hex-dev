#!/usr/bin/env python3
"""Render report tables from the retained observations; never rerun a sample."""
import json
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


def spread(values):
    return f'{statistics.median(values):.3f} [{min(values):.3f}, {max(values):.3f}]'


def tables(directory):
    rows = [json.loads(line) for line in (directory / 'runs.jsonl').read_text().splitlines()]
    assert len(rows) == 99
    for row in rows:
        assert row['exit_code'] == 0 and not row['timed_out'], row['log']
        assert not any('error' in key for key in row), row['log']
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
    meta = json.loads((HERE / 'kernel-inputs.json').read_text())
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
                      f'{m["sturm_max_height"].bit_length()} | {statistics.median(a.values()):.3f} | '
                      f'{statistics.median(b.values()):.3f} | {spread([b[i] - a[i] for i in range(4)])} |')
    inputs = dict(zip(list(NAMES), ['3/5', '2/1', '2/2', '2/64', '2/6', '2/2', '4/2']))
    solver = ['| Example | Levels | Input d/H | Result | Cell explanations | Projected factors per explanation, in order | Learned clauses | Invocation ms |',
              '|---|---:|---|---|---:|---|---:|---:|']
    for r in rows:
        if r['kind'] != 'solver':
            continue
        example = r['example']
        counts = ', '.join(str(e['projection_count']) for e in r['explanations']) or '—'
        solver.append(f'| {NAMES[example][0]} | {3 if example == "sphere" else 2} | {inputs[example]} | '
                      f'{", ".join(r["result"])} | {len(r["explanations"])} | {counts} | '
                      f'{len(r["learned_clauses"])} | {r["wall_ns"] / 1e6:.3f} |')
    return {'LIFT_TABLE': '\n'.join(lift), 'KERNEL_TABLE': '\n'.join(kernel), 'SOLVER_TABLE': '\n'.join(solver)}


if __name__ == '__main__':
    for label, table in tables(Path(sys.argv[1])).items():
        print(f'<!-- {label} -->\n{table}\n')
