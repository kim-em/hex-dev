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
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def literal_bytes(value):
    return len(json.dumps(value, separators=(',', ':'), ensure_ascii=False).encode())


class Field:
    def __init__(self, depth, monic=False):
        from flint import fmpq_poly
        require(type(depth) is int and 1 <= depth <= 8, 'unsupported depth')
        self.depth = depth
        self.monic = monic
        self.x = fmpq_poly([0, 1])
        # Eisenstein at 2 proves this is a field. Its positive root is in (1,2).
        self.modulus = self.x ** (2 ** depth) - 2

    def alpha(self, level):
        return (self.x ** (2 ** (self.depth - level)) / (1 if self.monic else 2)) % self.modulus

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
    for flag in ('value_roundtrip', 'roots_replayed', 'query_replayed'):
        require(row.get(flag) is True, f'unchecked native {flag}')
    monic = row.get("monic", False)
    require(type(monic) is bool, "invalid monic family flag")
    if monic:
        require(row["eager"] is False, "monic family uses production packing")
        flags = row.get("production_reductions")
        require(isinstance(flags, list) and len(flags) == depth and
                all(type(flag) is bool and flag is True for flag in flags),
                "monic production reduction was not enabled")
    field = Field(depth, monic)
    require(isinstance(row['heads'], list) and len(row['heads']) == depth,
            'missing defining heads')
    for level, raw in enumerate(row['heads'], 1):
        require(isinstance(raw, list) and len(raw) == 4, 'wrong defining degree')
        coefficients = [field.value(coefficient, level - 1) for coefficient in raw]
        parent = field.alpha(level - 1)
        leading = 1 if monic else 2
        require(coefficients == [3 * parent, -parent, -3 * leading + field.x * 0,
                                 leading + field.x * 0],
                'different defining polynomial')
        alpha = field.alpha(level)
        require(leading * alpha ** 2 % field.modulus == parent, 'wrong tower relation')
    actual = field.value(row['value'], depth)
    alpha = field.alpha(depth)
    expected = ((1 + alpha) ** steps * field.inverse(alpha - 3)) % field.modulus
    require(actual == expected, 'stored value disagrees with exact field arithmetic')
    # Nonmonic: alpha_0=1 and alpha_i=sqrt(alpha_(i-1)/2) in (0,1).
    # Monic: alpha_0=2 and alpha_i=sqrt(alpha_(i-1)) in (1,2).
    # The other roots are -alpha_i and 3, outside the selected interval. Thus
    # (1+alpha_depth)^steps is positive and alpha_depth-3 is negative.
    require(type(row['sign']) is int and row['sign'] == -1, 'wrong selected-root sign')
    require(isinstance(row['roots'], list) and len(row['roots']) == depth,
            'missing root evidence')
    stored = growth(row['value'], depth)
    require(not (row['eager'] or monic) or all(d < 3 for d in stored['max_degree_by_level']),
            'value was not reduced at every enabled level')
    residue = [[int(q.numerator), int(q.denominator)] for q in actual]
    return dict(depth=depth, steps=steps, eager=row['eager'],
                **({'monic': True, 'production_reductions_checked': True} if monic else {}),
                exact_value_checked=True,
                selected_root_sign_checked=True, field_residue=residue,
                stored=stored,
                roots=[graph_statistics(packet) for packet in row['roots']],
                query=graph_statistics(row['query']))


def trace_data(path):
    """Count callback diagnostics strictly between the workload markers."""
    active = False
    started = ended = 0
    counts = Counter()
    aggregate = None
    operations = None
    for line in Path(path).read_text().splitlines():
        if line == 'NESTED BEGIN':
            require(not active and started == 0, 'duplicate workload start')
            active = True
            started += 1
        elif line == 'NESTED END':
            require(active, 'workload end without start')
            active = False
            ended += 1
        elif line.startswith('NESTED COUNTERS '):
            require(ended == 1 and not active and operations is None, 'misplaced operation counters')
            operations = json.loads(line.removeprefix('NESTED COUNTERS '))
            keys = {'poly_gcd', 'poly_xgcd', 'poly_xgcd_left', 'poly_pseudo_gcd',
                    'lean_nat_gcd', 'gmp_gcd', 'gmp_gcdext'}
            require(isinstance(operations, dict) and set(operations) == keys and
                    all(type(value) is int and value >= 0 for value in operations.values()),
                    'bad operation counters')
        elif line.startswith('NESTED CALLBACKS '):
            require(ended == 1 and not active and aggregate is None, 'misplaced callback aggregate')
            packet = json.loads(line.removeprefix('NESTED CALLBACKS '))
            require(packet.get('overflow') is False, 'callback counter overflow')
            aggregate = packet.get('counts')
            require(isinstance(aggregate, dict) and all(
                len(key.split(':')) == 2 and key.split(':')[0].isdecimal() and
                key.split(':')[1] in {'add', 'sub', 'neg', 'mul', 'inv', 'div', 'sign', 'zero',
                                      'eq', 'split', 'inverse_gcd', 'inverse_xgcd'} and
                type(value) is int and value >= 0 for key, value in aggregate.items()),
                'bad callback aggregate')
        elif active and line.startswith('NESTED '):
            _, depth, operation = line.split()
            require(depth.isdecimal(), 'invalid callback depth')
            counts[f'{depth}:{operation}'] += 1
    require(started == ended == 1 and not active, 'incomplete workload trace')
    if aggregate is not None:
        require(not counts or dict(counts) == aggregate, 'callback trace disagrees with aggregate')
        require(operations is not None, 'missing operation counters')
        counts = aggregate
    return dict(callback_counts=dict(sorted(counts.items())), operation_counts=operations)


def trace_counts(path):
    return trace_data(path)['callback_counts']


def verify_pairs(rows, results, unpaired=False):
    groups = {}
    for row, result in zip(rows, results):
        groups.setdefault((row['depth'], row['steps'], row.get('monic', False)), []).append((row, result))
    for pair in groups.values():
        monic = pair[0][0].get('monic', False)
        require(len(pair) == 2 or ((unpaired or monic) and len(pair) == 1),
                'unmatched policy pair')
        if len(pair) == 2:
            (a, ra), (b, rb) = pair
            require(a['eager'] != b['eager'], 'duplicate policy')
            require(a['heads'] == b['heads'], 'different literal defining heads')
            require(ra['field_residue'] == rb['field_residue'], 'policy values disagree')


def validate_trace(row, trace):
    counts = trace['callback_counts']
    depth, steps = row['depth'], row['steps']
    require(all(int(key.split(':')[0]) <= depth for key in counts), 'trace has deeper context')
    require(counts.get(f'{depth}:mul', 0) == steps + 1, 'trace product count disagrees with row')
    for operation in ['add', 'sub', 'inv', 'div', 'split', 'inverse_gcd', 'inverse_xgcd']:
        require(counts.get(f'{depth}:{operation}', 0) == 1, f'trace {operation} disagrees with row')
    operations = trace['operation_counts']
    if operations is not None:
        require(operations['poly_gcd'] == sum(value for key, value in counts.items()
                                              if key.endswith(':inverse_gcd')),
                'polynomial gcd does not match observed inverse sites')
        require(operations['poly_xgcd_left'] == sum(value for key, value in counts.items()
                                                    if key.endswith(':inverse_xgcd')),
                'polynomial xgcdLeft does not match observed inverse sites')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs', nargs='*', type=Path)
    parser.add_argument('--trace', action='append', default=[], type=Path)
    parser.add_argument('--unpaired', action='store_true', help='allow a single diagnostic arm')
    args = parser.parse_args()
    require(not args.trace or len(args.trace) == len(args.inputs), 'one trace per explicit input required')
    texts = [path.read_text() for path in args.inputs] if args.inputs else [sys.stdin.read()]
    results, all_rows = [], []
    for index, text in enumerate(texts):
        rows = [json.loads(line) for line in text.splitlines() if line.startswith('{')]
        require(bool(rows), 'missing functional rows')
        require(not args.trace or len(rows) == 1, 'one traced row per input required')
        for row in rows:
            checked = verify(row)
            if args.trace:
                trace = trace_data(args.trace[index])
                validate_trace(row, trace)
                checked.update(trace)
            results.append(checked)
            all_rows.append(row)
    verify_pairs(all_rows, results, args.unpaired)
    print(json.dumps(dict(oracle='python-flint', version=version('python-flint'),
                         results=results), sort_keys=True))


if __name__ == '__main__':
    main()
