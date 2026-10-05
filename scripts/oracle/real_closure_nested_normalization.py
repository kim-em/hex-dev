#!/usr/bin/env python3
"""Exact field checks and representation diagnostics for nested normalization.

These checks use Q(gamma), gamma^(2^depth)=2, independently of Hex root
selection, Sturm queries and inversion. Evidence statistics validate graph
structure only; mathematical certificate replay belongs to the Lean checker.
No elapsed time or asymptotic conclusion is derived here.
"""
from __future__ import annotations

import argparse
from collections import Counter
from importlib.metadata import version
import json
import math
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def literal_bytes(value):
    return len(json.dumps(value, separators=(',', ':'), ensure_ascii=False).encode())


class Field:
    def __init__(self, depth):
        from flint import fmpq_poly
        require(type(depth) is int and 1 <= depth <= 8, 'unsupported depth')
        self.depth = depth
        self.x = fmpq_poly([0, 1])
        # Eisenstein at 2 proves this is a field. Its positive root is in (1,2).
        self.modulus = self.x ** (2 ** depth) - 2

    def alpha(self, level):
        return (self.x ** (2 ** (self.depth - level)) / 2) % self.modulus

    def inverse(self, value):
        gcd, left, _ = value.xgcd(self.modulus)
        require(gcd.degree() == 0 and bool(gcd), 'zero field denominator')
        return (left / gcd[0]) % self.modulus

    def value(self, raw, level):
        from flint import fmpq, fmpq_poly
        require(isinstance(raw, list), 'coefficient must be an array')
        if level == 0:
            require(len(raw) == 2 and all(type(n) is int for n in raw),
                    'malformed rational pair')
            n, d = raw
            require(d > 0 and math.gcd(n, d) == 1, 'noncanonical rational')
            return fmpq_poly([fmpq(n, d)])
        require(not raw or raw[-1] != ([] if level > 1 else [0, 1]),
                'trailing literal zero')
        result = fmpq_poly([])
        alpha = self.alpha(level)
        for coefficient in reversed(raw):
            result = (result * alpha + self.value(coefficient, level - 1)) % self.modulus
        return result


def growth(raw, level):
    leaves = []
    degrees = [[] for _ in range(level)]

    def visit(value, depth):
        if depth == 0:
            leaves.append(value)
        else:
            degrees[depth - 1].append(len(value) - 1)
            for coefficient in value:
                visit(coefficient, depth - 1)

    visit(raw, level)
    return dict(rational_coefficients=len(leaves),
                max_numerator_bits=max((abs(n).bit_length() for n, _ in leaves), default=0),
                max_denominator_bits=max((d.bit_length() for _, d in leaves), default=0),
                total_coefficient_bits=sum(abs(n).bit_length() + d.bit_length() for n, d in leaves),
                max_degree_by_level=[max(values, default=-1) for values in degrees],
                serialized_bytes=literal_bytes(raw))


def graph_statistics(packet):
    require(isinstance(packet, list) and len(packet) == 3, 'bad graph packet')
    occurrences, claimed_nodes, graph = packet
    require(type(occurrences) is int and type(claimed_nodes) is int, 'bad graph counts')
    require(isinstance(graph, list) and len(graph) == 3 and type(graph[0]) is int
            and graph[0] == 1, 'unsupported graph format')
    _, root, entries = graph
    require(isinstance(entries, list) and type(root) is int and 0 <= root < len(entries),
            'graph root out of range')
    require(claimed_nodes == len(entries), 'wrong graph node count')
    expanded = []
    for index, entry in enumerate(entries):
        require(isinstance(entry, list) and len(entry) == 2, 'bad graph entry')
        children = entry[1]
        require(isinstance(children, list) and len(children) <= 1, 'bad optional children')
        count = 1
        if children:
            pair = children[0]
            require(isinstance(pair, list) and len(pair) == 2 and
                    all(type(child) is int and 0 <= child < index for child in pair),
                    'non-earlier graph child')
            count += sum(expanded[child] for child in pair)
        expanded.append(count)
    require(occurrences == expanded[root], 'wrong expanded tree count')
    return dict(tree_occurrences=occurrences, dag_nodes=len(entries),
                graph_serialized_bytes=literal_bytes(graph),
                structural_check=True, mathematical_replay_checked=False)


def verify(row):
    require(version('python-flint') == '0.9.0', 'python-flint 0.9.0 required')
    depth, steps = row['depth'], row['steps']
    require(type(steps) is int and steps >= 0, 'invalid steps')
    require(type(row['eager']) is bool, 'invalid policy')
    require(type(row['hash']) is int and 0 <= row['hash'] < 2 ** 64, 'invalid observed hash')
    field = Field(depth)
    require(isinstance(row['heads'], list) and len(row['heads']) == depth,
            'missing defining heads')
    for level, raw in enumerate(row['heads'], 1):
        require(isinstance(raw, list) and len(raw) == 4, 'wrong defining degree')
        coefficients = [field.value(coefficient, level - 1) for coefficient in raw]
        parent = field.alpha(level - 1)
        require(coefficients == [3 * parent, -parent, -6 + field.x * 0, 2 + field.x * 0],
                'different defining polynomial')
        alpha = field.alpha(level)
        require(2 * alpha ** 2 % field.modulus == parent, 'wrong tower relation')
    actual = field.value(row['value'], depth)
    alpha = field.alpha(depth)
    expected = ((1 + alpha) ** steps * field.inverse(alpha - 3)) % field.modulus
    require(actual == expected, 'stored value disagrees with exact field arithmetic')
    # alpha_0=1 and alpha_i=sqrt(alpha_(i-1)/2) uniquely in (0,1).
    # The other roots are -alpha_i and 3, both outside (0,1). Consequently
    # (1+alpha_depth)^steps is positive and alpha_depth-3 is negative.
    require(type(row['sign']) is int and row['sign'] == -1, 'wrong selected-root sign')
    require(isinstance(row['roots'], list) and len(row['roots']) == depth,
            'missing root evidence')
    residue = [[int(q.numerator), int(q.denominator)] for q in actual]
    return dict(depth=depth, steps=steps, eager=row['eager'], exact_value_checked=True,
                selected_root_sign_checked=True, field_residue=residue,
                stored=growth(row['value'], depth),
                roots=[graph_statistics(packet) for packet in row['roots']],
                query=graph_statistics(row['query']))


def trace_counts(path):
    """Count callback diagnostics strictly between the workload markers."""
    active = False
    started = ended = 0
    counts = Counter()
    for line in Path(path).read_text().splitlines():
        if line == 'NESTED BEGIN':
            require(not active and started == 0, 'duplicate workload start')
            active = True
            started += 1
        elif line == 'NESTED END':
            require(active, 'workload end without start')
            active = False
            ended += 1
        elif active and line.startswith('NESTED '):
            _, depth, operation = line.split()
            require(depth.isdecimal(), 'invalid callback depth')
            counts[f'{depth}:{operation}'] += 1
    require(started == ended == 1 and not active, 'incomplete workload trace')
    return dict(sorted(counts.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs', nargs='+', type=Path)
    parser.add_argument('--trace', action='append', default=[], type=Path)
    args = parser.parse_args()
    require(not args.trace or len(args.trace) == len(args.inputs), 'one trace per input required')
    results = []
    for index, path in enumerate(args.inputs):
        rows = [json.loads(line) for line in path.read_text().splitlines() if line.startswith('{')]
        require(bool(rows), 'missing functional rows')
        require(not args.trace or len(rows) == 1, 'one traced row per input required')
        for row in rows:
            checked = verify(row)
            if args.trace:
                checked['callback_counts'] = trace_counts(args.trace[index])
            results.append(checked)
    if len(results) == 2:
        require(results[0]['depth'] == results[1]['depth'] and
                results[0]['steps'] == results[1]['steps'] and
                results[0]['eager'] != results[1]['eager'], 'unmatched policy pair')
        require(results[0]['field_residue'] == results[1]['field_residue'], 'policy values disagree')
    print(json.dumps(dict(oracle='python-flint', version=version('python-flint'),
                         results=results), sort_keys=True))


if __name__ == '__main__':
    main()
