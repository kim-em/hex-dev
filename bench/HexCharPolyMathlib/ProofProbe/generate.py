#!/usr/bin/env python3
"""Generate the list Berkowitz premise probes for issue #10212.

Run from the repository root. Each input is a square signed 8-bit matrix
seeded with 10212 + its dimension. These are checker-only diagnostics;
they do not assert a characteristic-polynomial soundness theorem.
"""
from pathlib import Path
import random

ROOT = Path('bench/HexCharPolyMathlib/ProofProbe')


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def certify(matrix):
    if not matrix:
        return [], [1]
    a, *r = matrix[0]
    block = [row[1:] for row in matrix[1:]]
    w = [row[0] for row in matrix[1:]]
    steps, previous = certify(block)
    column, vectors = [1, -a], []
    for j in range(len(r)):
        column.append(-dot(r, w))
        if j + 1 < len(r):
            w = [dot(row, w) for row in block]
            vectors.append(w)
    coefficients = [dot(column[:i + 1][::-1], previous) for i in range(len(column))]
    return [(column, vectors, coefficients)] + steps, coefficients


def quoted(value):
    if isinstance(value, list):
        return '[' + ', '.join(map(quoted, value)) + ']'
    return f'(Int.ofNat {value})' if value >= 0 else f'(Int.negSucc {-value - 1})'


def generate():
    ROOT.mkdir(parents=True, exist_ok=True)
    options = ('set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
               'set_option profiler true\nset_option profiler.threshold 1000000\n')
    for n in [4, 8, 16, 32]:
        rng = random.Random(10212 + n)
        matrix = [[rng.randrange(-128, 128) for _ in range(n)] for _ in range(n)]
        steps, coefficients = certify(matrix)
        for arm in ['Check', 'Block', 'Quoted', 'Computed']:
            literal = quoted if arm in ['Quoted', 'Computed'] else str
            support = {'Block': 'BlockSupport', 'Computed': 'ComputedSupport'}.get(arm, 'Support')
            namespace = {'Block': 'CharPolyBlockProbe', 'Computed': 'CharPolyComputedProbe'}.get(arm, 'CharPolyProbe')
            tactic = {'Block': 'check_block_kernel', 'Computed': 'check_computed_kernel'}.get(arm, 'check_kernel')
            entries = []
            for i, (column, vectors, result) in enumerate(steps):
                block = [row[i + 1:] for row in matrix[i + 1:]]
                prefix = 'block := ' + str(block) + ', ' if arm == 'Block' else ''
                entries.append('{ ' + prefix + 'column := ' + literal(column) +
                               ('' if arm == 'Computed' else ', vectors := ' + literal(vectors)) +
                               ', coefficients := ' + literal(result) + ' }')
            witness = '[' + ',\n'.join(entries) + ']'
            source = (f'import HexCharPolyMathlib.ProofProbe.{support}\n' + options +
                      f'open {namespace}\ntheorem result : check {n} {literal(matrix)} '
                      f'{witness} {literal(coefficients)} = true := by {tactic}\n'
                      '#print axioms result\n')
            (ROOT / f'Dense{n}{arm}.lean').write_text(source)
        matrix_literal = '!![' + '; '.join(', '.join(map(str, r)) for r in matrix) + ']'
        source = ('import HexRankMathlib\n' + options +
                  f'theorem result : Matrix.rank (R := ℤ) {matrix_literal} = {n} := by rank\n'
                  '#print axioms result\n')
        (ROOT / f'Dense{n}Rank.lean').write_text(source)
    for src, dst in [('Dense16Quoted', 'Dense16Candidate'), ('Dense16Rank', 'Dense16Reference')]:
        source = (ROOT / (src + '.lean')).read_text()
        source = ''.join(line for line in source.splitlines(keepends=True)
                         if not line.startswith('set_option profiler'))
        (ROOT / (dst + '.lean')).write_text(source)


if __name__ == '__main__':
    generate()
