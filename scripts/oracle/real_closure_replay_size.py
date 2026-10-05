#!/usr/bin/env python3
"""Exact selected-root inputs and DAG/tree sizes; no timing conclusions.

Native certificate replay checks mathematical evidence. This independent
checker validates the input meanings, graph bindings and query slices, and
computes payload sizes from compact UTF-8 JSON, excluding transport whitespace.
"""
from __future__ import annotations
import argparse
import json
import math
import sys
from pathlib import Path
from importlib.metadata import version
from flint import fmpq, fmpq_poly


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bytes_of(value):
    return len(json.dumps(value, separators=(',', ':'), ensure_ascii=False).encode())


def value(raw, level, gamma, modulus, leaves):
    require(isinstance(raw, list), 'coefficient is not an array')
    if level == 0:
        require(len(raw) == 3 and raw[0] == 0 and all(type(x) is int for x in raw),
                'invalid rational coefficient')
        _, n, d = raw
        require(d > 0 and math.gcd(n, d) == 1, 'noncanonical rational')
        leaves.append((n, d))
        return fmpq_poly([fmpq(n, d)])
    if not raw:
        return fmpq_poly([])
    require(len(raw) == 2 and isinstance(raw[0], list) and type(raw[1]) is int
            and raw[1] in (-1, 1), 'invalid packed algebraic coefficient')
    # The only algebraic coefficient level is alpha_1 = gamma^2 at depth 2.
    alpha = gamma ** 2 % modulus
    result = fmpq_poly([])
    for coefficient in reversed(raw[0]):
        result = (result * alpha + value(coefficient, level - 1, gamma, modulus, leaves)) % modulus
    nonzero = [(i, coefficient) for i, coefficient in enumerate(result) if coefficient]
    require(len(nonzero) == 1 and nonzero[0][0] in (0, 2),
            'unsupported input algebraic coefficient')
    require(raw[1] == (1 if nonzero[0][1] > 0 else -1), 'wrong input cached sign')
    return result


def verify(row):
    require(version('python-flint') == '0.9.0', 'python-flint 0.9.0 required')
    depth, count, repeated = row['depth'], row['queries_count'], row['repeated']
    require(type(depth) is int and depth in (1, 2), 'invalid depth')
    require(type(count) is int and count in (1, 2, 4, 8, 16, 32), 'invalid query count')
    require(type(repeated) is bool and row['replayed'] is True, 'missing native replay')
    gamma = fmpq_poly([0, 1])
    modulus = gamma ** (2 ** depth) - 2
    leaves = []
    def polynomial(raw):
        require(isinstance(raw, list), 'polynomial is not an array')
        return [value(c, depth - 1, gamma, modulus, leaves) for c in raw]
    head = polynomial(row['head'])
    require(head == [-fmpq_poly([2]) if depth == 1 else -(gamma ** 2),
                     fmpq_poly([]), fmpq_poly([1])], 'changed defining polynomial')
    require(len(row['queries']) == count, 'query count mismatch')
    for i, raw in enumerate(row['queries']):
        require(polynomial(raw) == [fmpq_poly([-1 if repeated else -i]), fmpq_poly([1])],
                'changed linear query')
    require(row['signs'] == [1 if repeated or i < 2 else -1 for i in range(count)]
            and all(type(s) is int for s in row['signs']), 'wrong selected signs')
    # Positive roots of X^2-2 and X^4-2 both lie strictly between 1 and 2.
    graph = row['graph']
    require(isinstance(graph, list) and len(graph) == 3 and type(graph[0]) is int and graph[0] == 1,
            'invalid graph version')
    _, root, entries = graph
    require(type(root) is int and isinstance(entries, list) and 0 <= root < len(entries),
            'invalid graph root')
    nodes, expanded_bytes, child_edges, payload_bytes = [], [], [], []
    expected_context = entries[root][0][0]
    require(expected_context == [0], 'unknown context reference')
    for i, entry in enumerate(entries):
        require(isinstance(entry, list) and len(entry) == 2, 'invalid graph entry')
        node, children = entry
        require(isinstance(node, list) and len(node) == 11, 'invalid node shape')
        require(node[0] == expected_context and node[1] == row['head'], 'stale node binding')
        require(node[2] == entries[root][0][2] and node[3] == entries[root][0][3],
                'changed node endpoints')
        require(isinstance(children, list) and len(children) <= 1, 'invalid optional children')
        links = children[0] if children else []
        require(isinstance(links, list) and len(links) in (0, 2)
                and all(type(j) is int and 0 <= j < i for j in links), 'non-earlier child')
        if links:
            half = len(node[4]) // 2
            require(len(node[4]) > 1 and entries[links[0]][0][4] == node[4][:half]
                    and entries[links[1]][0][4] == node[4][half:], 'changed query slice')
        else:
            require(len(node[4]) <= 1, 'oversized leaf')
        size = bytes_of(node)
        payload_bytes.append(size)
        child_edges.append(links)
        nodes.append(1 + sum(nodes[j] for j in links))
        expanded_bytes.append(size + sum(expanded_bytes[j] for j in links))
    require(entries[root][0][4] == row['queries'], 'changed root queries')
    reached, pending = set(), [root]
    while pending:
        i = pending.pop()
        if i not in reached:
            reached.add(i)
            pending.extend(child_edges[i])
    require(len(reached) == len(entries), 'unreachable graph entries')
    edges = sum(map(len, child_edges))
    for name, expected in [('dag_nodes', len(entries)), ('dag_edges', edges),
                           ('tree_occurrences', nodes[root])]:
        require(type(row[name]) is int and row[name] == expected, f'wrong {name}')
    return dict(depth=depth, queries_count=count, repeated=repeated, dag_nodes=len(entries),
                dag_edges=edges, tree_occurrences=nodes[root], graph_compact_bytes=bytes_of(graph),
                unique_node_payload_bytes=sum(payload_bytes),
                unshared_node_payload_bytes=expanded_bytes[root],
                input_rational_leaves=len(leaves),
                input_rational_bits=sum(abs(n).bit_length() + d.bit_length() for n, d in leaves),
                input_max_numerator_bits=max(abs(n).bit_length() for n, _ in leaves),
                mathematical_replay_checked=False, exact_inputs_checked=True)


def check_rows(rows):
    results = [verify(row) for row in rows]
    keys = [(r['depth'], r['queries_count'], r['repeated']) for r in results]
    require(len(keys) == len(set(keys)) and len(keys) == 24, 'incomplete or duplicate family')
    return dict(format=1, rows=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path)
    args = parser.parse_args()
    text = args.input.read_text() if args.input else sys.stdin.read()
    rows = [json.loads(line) for line in text.splitlines()]
    print(json.dumps(check_rows(rows), indent=2))


if __name__ == '__main__':
    main()
