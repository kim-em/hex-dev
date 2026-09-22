#!/usr/bin/env python3
"""Generate the fixed two-stage packed determinant comparison, retaining the old ladder."""
from __future__ import annotations
import functools
import itertools
import json
import math
from pathlib import Path
import re
import sys

import sympy as sp

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import det_symbolic_probes as original

DEST = original.DEST
PREFIX = original.PREFIX
MANIFEST = ROOT / 'scripts/bench/det_packed_manifest.json'
INPUTS = ROOT / 'bench/HexPolyDet/packed-inputs'
original.polynomial = functools.lru_cache(None)(original.polynomial)


def rows_json(a, k, p=0):
    xs = sp.symbols(f'x0:{k}')
    result = []
    for row in a:
        polys = [sp.Poly(sp.sympify(re.sub(r'\bx\b', 'x0', e.replace('^', '**').replace('ClosedAlgebraic.α', 'x0'))), *xs) for e in row]
        scale = sp.ilcm(*[c.q for f in polys for c in f.coeffs()], 1)
        result.append([[[list(m), int(c * scale) % p if p else int(c * scale)]
                        for m, c in f.terms() if (int(c * scale) % p if p else c)] for f in polys])
    return result


def source_case(case, a, rhs, k, carrier='Int'):
    binders = '(' + ' '.join(f'x{i}' for i in range(k)) + f' : {carrier})'
    imports = 'import HexPolyDetMathlib.Tactic\n'
    if carrier.startswith('ZMod'):
        imports += 'import Mathlib.Algebra.Field.ZMod\n'
    if carrier == 'ZMod 2147483647':
        imports += 'import HexPolyDetMathlib.ProofProbe.ResidueSupport\n'
    return original.HEADER + imports + f'''set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem result {binders} : Matrix.det (R := {carrier}) ({original.literal(a)}) = {rhs} := by
  det

#print axioms result
'''


def original_rows(case, source):
    n, k = case['dimension'], case['atoms']
    if case['family'] == 'literal-function':
        return [[f'x0 + {int(i == j)}' for j in range(n)] for i in range(n)]
    if case['family'] == 'literal-array':
        return [['x0' if i == j else '1' if abs(i-j) == 1 else '0' for j in range(n)] for i in range(n)]
    match = re.search(r'!!\[(.*?)\]', source, re.S)
    if not match:
        raise ValueError(case['stem'])
    return [[e.strip() for e in row.split(',')] for row in match[1].split(';')]


def main():
    INPUTS.mkdir(parents=True, exist_ok=True)
    old = json.loads((ROOT / 'scripts/bench/det_symbolic_manifest.json').read_text())
    cases, infeasible = [], list(old['infeasible'])
    sources = {}
    for case in old['cases']:
        case = dict(case)
        source = (DEST / (case['stem'] + 'Hex.lean')).read_text()
        a = original_rows(case, source)
        cases.append(case)
        sources[case['stem']] = source
        (INPUTS / (case['stem'] + '.json')).write_text(json.dumps(dict(n=case['dimension'], k=case['atoms'], rows=rows_json(a, case['atoms']), p=0, missing=False)) + '\n')
    stems = {c['stem'] for c in cases}
    for n, k, d, support in itertools.product([4, 8, 16], [1, 2, 3, 4], [2, 4, 8, 16], [1, 4, 16]):
        stem = f'N{n}K{k}D{d}S{support}'
        if stem in stems:
            continue
        case = dict(stem=stem, family='dense-row-scaled', dimension=n, atoms=k, degree=d, support=support, carrier='Int')
        if support > math.comb(k+d, d):
            infeasible.append(dict(case, reason='support exceeds the number of monomials'))
            continue
        a, rhs = original.dense(n,k,d,support)
        sources[stem] = source_case(case,a,rhs,k)
        cases.append(case)
        (INPUTS / (stem + '.json')).write_text(json.dumps(dict(n=n,k=k,rows=rows_json(a,k),p=0,missing=False))+'\n')
    # A dense four-by-four block and an independent final diagonal have 17 atoms.
    # The final prefix exceeds 65536 digits while the term-list witness stays small.
    a = [[f'x{4*i+j}' if i<4 and j<4 else 'x16' if i==j else '0' for j in range(5)] for i in range(5)]
    rhs = str(sp.det(sp.Matrix([[sp.Symbol(f'x{4*i+j}') for j in range(4)] for i in range(4)]))).replace('**','^') + ' ) * x16'
    rhs = '(' + rhs
    special = [('Independent5', 'independent-atoms', a, rhs, 17, 'Int', 0, False)]
    block = [['x0','1','0','0'], ['1','x0','0','0'], ['0','0','x1','1'], ['0','0','1','x1']]
    special.append(('Block4', 'block-diagonal', block, '(x0^2-1)*(x1^2-1)', 2, 'Int', 0, False))
    for p in [3,2147483647]:
        for missing in [False,True]:
            stem = f'Residue{p}' + ('Missing' if missing else '')
            special.append((stem, 'residue-missing' if missing else 'residue-quotient', block, '(x0^2-1)*(x1^2-1)', 2, f'ZMod {p}', p, missing))
    for stem,family,a,rhs,k,carrier,p,missing in special:
        case = dict(stem=stem,family=family,dimension=len(a),atoms=k,carrier=carrier,modulus=p,missing=missing)
        sources[stem] = source_case(case,a,rhs,k,carrier)
        cases.append(case)
        (INPUTS/(stem+'.json')).write_text(json.dumps(dict(n=len(a),k=k,rows=rows_json(a,k,p),p=p,missing=missing))+'\n')
    for case in cases:
        case.update(samples=6,cleanup_timeout_seconds=45,proof_build_ceiling_ms=45000)
        source = sources[case['stem']]
        for arm, mode in [('Lists',1),('Packed',2),('Dispatch',0),('Mathlib',None)]:
            if arm == 'Mathlib':
                old_file = DEST/(case['stem']+'Mathlib.lean')
                text = old_file.read_text() if old_file.exists() else source.replace('import HexPolyDetMathlib.Tactic','import Mathlib.Tactic.NormDet').replace('  det\n','  simp only [norm_det] <;> ring\n')
            else:
                text = source.replace('set_option trace.HexMatrix.certificate true\n','')
                text = text.replace('theorem result', f'set_option trace.HexMatrix.certificate true\nset_option hex.det.checker {mode}\n' + ('set_option hex.det.quotients false\n' if case.get('missing') else '') + 'theorem result')
            text = text.replace('theorem result','set_option profiler true\nset_option profiler.threshold 1000000\n\ntheorem result')
            path = DEST/f'Packed{case["stem"]}{arm}.lean'
            path.write_text(text)
            imports = '\n'.join(line for line in text.splitlines() if line.startswith('import '))
            (DEST/f'Packed{case["stem"]}{arm}Baseline.lean').write_text(original.HEADER+imports+'\n')
    profiles = {}
    for c in cases:
        profiles.setdefault(c['family'], c['stem'])
    for c in cases:
        if c['dimension'] >= 4 and next(x for x in cases if x['stem'] == profiles[c['family']])['dimension'] < 4:
            profiles[c['family']] = c['stem']
    profiles['dense-row-scaled'] = 'N4K2D2S4'
    for family, stem in profiles.items():
        source = (DEST/f'Packed{stem}Dispatch.lean').read_text().replace('profiler.threshold 1000000','profiler.threshold 0')
        (DEST/f'Packed{stem}Profile.lean').write_text(source)
    MANIFEST.write_text(json.dumps(dict(schema='hex-det-packed-v1',cases=cases,infeasible=infeasible,
        crossover_rule='retain historical list keys; add separate list/tree keys from eligible witnesses with six complete samples per arm and 0 < packed median < term-list median',
        crossover_keys=['packedBits','leftSupport','rightSize','resultSupport','inner'],
        limits=dict(digits=65536,bits=16777216,seconds=45), profiles=profiles,
        schedule='six adjacent pairs, trial-major rotation, AB/BA, retained failures and declines',
        stages=['forced term-list versus forced packed on identical witnesses','Hex-only fixed-table dispatch versus unmodified Mathlib norm_det; declines are not completions']),indent=2)+'\n')
    print(f'{len(cases)} cases; {len(infeasible)} infeasible cells; {len(profiles)} profiles')

if __name__ == '__main__':
    main()
