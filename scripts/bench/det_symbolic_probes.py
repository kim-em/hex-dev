#!/usr/bin/env python3
"""Generate the preregistered symbolic determinant ladder and its identical targets.

The dense ladder scales the rows of seeded dense integer matrices by sparse
polynomials. This controls entry degree/support without requiring the generator
to expand determinants. The report must retain this correlation between entries.
The 2x2, four-atom, linear monomial case uses four independent entries instead.
"""
from __future__ import annotations

import itertools
import json
import math
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / 'bench/HexPolyDetMathlib/ProofProbe'
HEADER = '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
'''
PREFIX = 'HexPolyDetMathlib.ProofProbe'


def determinant(a):
    a = [r[:] for r in a]
    prev, sign = 1, 1
    for i in range(len(a) - 1):
        p = next((j for j in range(i, len(a)) if a[j][i]), None)
        if p is None:
            return 0
        if p != i:
            a[p], a[i] = a[i], a[p]
            sign = -sign
        pivot = a[i][i]
        for j in range(i + 1, len(a)):
            for k in range(i + 1, len(a)):
                a[j][k] = (pivot * a[j][k] - a[j][i] * a[i][k]) // prev
            a[j][i] = 0
        prev = pivot
    return sign * a[-1][-1]


def monomial(m):
    return ' * '.join(f'x{i}' if e == 1 else f'x{i} ^ {e}' for i, e in enumerate(m) if e) or '1'


def polynomial(k, degree, support, row):
    monos = list(itertools.product(range(degree + 1), repeat=k))
    monos = [m for m in monos if sum(m) <= degree]
    rng = random.Random(10236 + 31 * row + 7 * k + degree)
    rng.shuffle(monos)
    lead = tuple(degree if i == row % k else 0 for i in range(k))
    # Rotate the preferred variables so the complete matrix uses the requested atoms.
    preferred = [lead] + [tuple(1 if i == (row + j) % k else 0 for i in range(k)) for j in range(k)]
    selected = list(dict.fromkeys(preferred + monos))[:support]
    return ' + '.join(f'{1 + (row + j) % 3} * ({monomial(m)})' for j, m in enumerate(selected))


def literal(a):
    return '!![' + '; '.join(', '.join(r) for r in a) + ']'


def dense(n, k, degree, support, rational=False):
    rng = random.Random(10236 + n)
    c = [[rng.choice([-3, -2, -1, 1, 2, 3]) for _ in range(n)] for _ in range(n)]
    while determinant(c) == 0:
        c[0][0] += 1
    fs = [polynomial(k, degree, support, i) for i in range(n)]
    if n == 2 and k == 4 and support == 1:
        if degree == 1:
            return [['x0', 'x1'], ['x2', 'x3']], 'x0 * x3 - x1 * x2'
        fs = ['x0 * x1' + (f' ^ {degree - 1}' if degree > 2 else ''),
              'x2 * x3' + (f' ^ {degree - 1}' if degree > 2 else '')]
    a = [[f'({c[i][j]}) * ({fs[i]})' for j in range(n)] for i in range(n)]
    rhs = f'({determinant(c)}) * ' + ' * '.join(f'({f})' for f in fs)
    if rational:
        a = [[f'({e}) / {i + 2}' for e in r] for i, r in enumerate(a)]
        rhs = f'({rhs}) / {math.prod(range(2, n + 2))}'
    return a, rhs


def write_case(stem, metadata, a, rhs, k, carrier='Int', support_import=False):
    extras = f'import {PREFIX}.AlgebraicSupport\n' if support_import else ''
    params = ' '.join(f'x{i}' for i in range(k))
    binders = f'({params} : {carrier})' if params else ''
    target = f'Matrix.det (R := {carrier}) {literal(a)} = {rhs}'
    for arm in ['Hex', 'Mathlib']:
        imp = 'HexPolyDetMathlib.Tactic' if arm == 'Hex' else 'Mathlib.Tactic.NormDet'
        options = ''
        tactic = 'det' if arm == 'Hex' else 'simp only [norm_det] <;> ring'
        body = f'''{HEADER}import {imp}
{extras}
{options}set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result {binders} : {target} := by
  {tactic}

#print axioms result
'''
        (DEST / f'{stem}{arm}.lean').write_text(body)
    metadata.update(stem=stem, atoms=1 if support_import else k, carrier=carrier, cleanup_timeout_seconds=45,
                    proof_build_ceiling_ms=45000, samples=6)
    return metadata


def main():
    DEST.mkdir(parents=True, exist_ok=True)
    cases, infeasible = [], []
    for n, k, d, s in itertools.product([2, 4, 8], [1, 2, 4], [1, 2, 4], [1, 4, 16]):
        meta = dict(family='dense-row-scaled', dimension=n, variables=k, degree=d, support=s)
        if s > math.comb(k + d, d):
            infeasible.append(dict(meta, reason='support exceeds the number of monomials'))
            continue
        a, rhs = dense(n, k, d, s)
        stem = f'N{n}K{k}D{d}S{s}'
        cases.append(write_case(stem, meta, a, rhs, k))
    for k, d, support in [(1, 1, 1), (2, 2, 4), (4, 4, 16)]:
        a, rhs = dense(3, k, d, support)
        cases.append(write_case(f'N3K{k}D{d}S{support}',
            dict(family='dense-row-scaled', dimension=3, variables=k, degree=d, support=support), a, rhs, k))
    for n in [2, 3, 4, 8]:
        a, rhs = dense(n, 2, 2, 4, rational=True)
        cases.append(write_case(f'Rational{n}', dict(family='rational', dimension=n, degree=2, support=4), a, rhs, 2, 'Rat'))
        a, rhs = dense(n, 2, 1, 1)
        a[-1] = a[0][:]
        cases.append(write_case(f'Singular{n}', dict(family='singular', dimension=n, degree=1, support=1), a, '0', 2))
        a = [['0' for _ in range(n)] for _ in range(n)]
        for i in range(0, n - 1, 2):
            a[i][i:i+2] = ['ClosedAlgebraic.α', '1']
            a[i+1][i:i+2] = ['2', 'ClosedAlgebraic.α']
        if n % 2:
            a[-1][-1] = '1'
        cases.append(write_case(f'Algebraic{n}', dict(family='closed-algebraic', dimension=n, degree=1, support=1),
                                a, f'(ClosedAlgebraic.α ^ 2 - 2) ^ {n // 2}', 0, 'ClosedAlgebraic.K', True))
    a, rhs = dense(4, 2, 2, 4)
    a[0][0] = '0'
    # Explicit block with a zero leading pivot and a nonzero polynomial determinant.
    a = [['0', 'x0', '0', '0'], ['x1', '1', '0', '0'],
         ['0', '0', 'x0', '1'], ['0', '0', '1', 'x1']]
    cases.append(write_case('Swaps', dict(family='pivot-swap', dimension=4), a, '-x0 * x1 * (x0 * x1 - 1)', 2))
    a = [['x0' if i == j else '1' if abs(i-j) == 1 else '0' for j in range(4)] for i in range(4)]
    cases.append(write_case('Tridiagonal', dict(family='structured', dimension=4), a, 'x0 ^ 4 - 3 * x0 ^ 2 + 1', 1))
    (DEST / 'AlgebraicSupport.lean').write_text(HEADER + '''import Mathlib.Algebra.QuadraticAlgebra.Basic
namespace ClosedAlgebraic
abbrev K := QuadraticAlgebra Rat 2 0
@[irreducible] def α : K := QuadraticAlgebra.omega
theorem square : α ^ 2 = 2 := by
  rw [α, pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl
end ClosedAlgebraic
''')
    for arm, imp in [('Hex', 'HexPolyDetMathlib.Tactic'), ('Mathlib', 'Mathlib.Tactic.NormDet')]:
        (DEST / f'{arm}Baseline.lean').write_text(HEADER + f'import {imp}\n')
        (DEST / f'{arm}AlgebraicBaseline.lean').write_text(HEADER + f'import {imp}\nimport {PREFIX}.AlgebraicSupport\n')
    # A scope probe measures the failed composed attempt before using the relation.
    for arm, imp in [('Hex', 'HexPolyDetMathlib.Tactic'), ('Mathlib', 'Mathlib.Tactic.NormDet')]:
        options = ''
        attempt = 'det' if arm == 'Hex' else 'simp only [norm_det] <;> ring'
        (DEST / f'AlgebraicScope{arm}.lean').write_text(HEADER + f"""import {imp}
import {PREFIX}.AlgebraicSupport
{options}
theorem result : Matrix.det !![ClosedAlgebraic.α, 1; 2, ClosedAlgebraic.α] = 0 := by
  fail_if_success (solve | {attempt})
  rw [Matrix.det_fin_two]
  change ClosedAlgebraic.α * ClosedAlgebraic.α - 1 * 2 = 0
  rw [← pow_two, ClosedAlgebraic.square, one_mul, sub_self]
#print axioms result
""")
        (DEST / f'Valuation{arm}.lean').write_text(HEADER + f"""import {imp}
{options}
theorem result (x : Int) (hx : x = 1) : Matrix.det !![x, 1; 1, x] = 0 := by
  have h : Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by
    {attempt}
  rw [h, hx]
  rfl
#print axioms result
""")
    cases += [dict(stem='AlgebraicScope', family='closed-algebraic-scope', dimension=2,
                   atoms=1, scope_probe=True, cleanup_timeout_seconds=45, proof_build_ceiling_ms=45000, samples=6),
              dict(stem='Valuation', family='valuation', dimension=2, atoms=1,
                   cleanup_timeout_seconds=45, proof_build_ceiling_ms=45000, samples=6)]
    manifest = dict(schema='hex-symbolic-det-probes-v1', cases=cases, infeasible=infeasible,
                    description=__doc__, default_simproc_enabled=False, small_formula_dimension=3,
                    limits=dict(dimension=16, certificate_terms=65536, coefficient_bits=4096,
                                source_nodes=100000, proof_nodes=1000000),
                    profile_cases=['N2K1D1S1', 'N3K2D2S4', 'N4K2D2S4', 'N8K4D4S16', 'Rational4', 'Singular4', 'Algebraic4', 'Swaps', 'Tridiagonal', 'Valuation', 'AlgebraicScope'])
    for stem in manifest['profile_cases']:
        source = (DEST / f'{stem}Hex.lean').read_text()
        source = source.replace('theorem result',
            'set_option profiler true\nset_option profiler.threshold 0\nset_option trace.HexMatrix.certificate true\n\ntheorem result')
        (DEST / f'{stem}Profile.lean').write_text(source)
    (ROOT / 'scripts/bench/det_symbolic_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'{len(cases)} feasible probes; {len(infeasible)} infeasible parameter combinations')


if __name__ == '__main__':
    main()
