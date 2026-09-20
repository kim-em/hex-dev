#!/usr/bin/env python3
"""Independent list normalization and exact rational Boolean interpretation.

Quantifier rows check binding metadata only. Rational samples do not certify
real quantified truth; that contract is covered by Lean equivalence proofs.
"""

from __future__ import annotations

from fractions import Fraction
import json
import sys


def natural(x: object) -> bool:
    return type(x) is int and x >= 0


def normalize(tree: dict, arity: int) -> dict:
    op = tree["op"]
    if op == "atom":
        if tree["cmp"] not in {"eq", "ne", "lt", "le", "gt", "ge"}:
            raise ValueError("unknown comparison")
        terms = {}
        for exponents, coefficient in tree["terms"]:
            # Validate before collecting: malformed zero terms still fail.
            if (len(exponents) != arity or not all(map(natural, exponents))
                    or type(coefficient) is not int):
                raise ValueError("malformed monomial")
            key = tuple(exponents)
            terms[key] = terms.get(key, 0) + coefficient
        return {"op": op, "cmp": tree["cmp"], "terms": [
            [list(key), terms[key]] for key in sorted(terms, reverse=True) if terms[key]]}
    if op in {"true", "false"}:
        return {"op": op}
    if op == "not":
        return {"op": op, "arg": normalize(tree["arg"], arity)}
    if op in {"and", "or"}:
        # Always visit both sides, even if one side determines the truth value.
        return {"op": op, "left": normalize(tree["left"], arity),
                "right": normalize(tree["right"], arity)}
    raise ValueError("unknown Boolean constructor")


def evaluate(tree: dict, point: list[Fraction]) -> bool:
    op = tree["op"]
    if op == "atom":
        value = Fraction(0)
        for exponents, coefficient in tree["terms"]:
            term = Fraction(coefficient)
            for x, exponent in zip(point, exponents, strict=True):
                term *= x ** exponent
            value += term
        return {"eq": value == 0, "ne": value != 0, "lt": value < 0,
                "le": value <= 0, "gt": value > 0, "ge": value >= 0}[tree["cmp"]]
    if op in {"true", "false"}:
        return op == "true"
    if op == "not":
        return not evaluate(tree["arg"], point)
    left, right = evaluate(tree["left"], point), evaluate(tree["right"], point)
    return (left and right) if op == "and" else (left or right)


def node_count(tree: dict) -> int:
    op = tree["op"]
    if op == "not":
        return 1 + node_count(tree["arg"])
    if op in {"and", "or"}:
        return 1 + node_count(tree["left"]) + node_count(tree["right"])
    return 1


def map_atoms(tree: dict, transform) -> dict:
    op = tree["op"]
    if op == "atom":
        return transform(tree)
    if op == "not":
        return {"op": op, "arg": map_atoms(tree["arg"], transform)}
    if op in {"and", "or"}:
        return {"op": op, "left": map_atoms(tree["left"], transform),
                "right": map_atoms(tree["right"], transform)}
    return tree


def nnf(tree: dict, negative: bool = False) -> dict:
    op = tree["op"]
    if op == "atom":
        complement = {"eq": "ne", "ne": "eq", "lt": "ge", "ge": "lt", "le": "gt", "gt": "le"}
        return dict(tree, cmp=complement[tree["cmp"]]) if negative else tree
    if op == "not":
        return nnf(tree["arg"], not negative)
    if op in {"true", "false"}:
        return {"op": ("false" if op == "true" else "true") if negative else op}
    return {"op": ("or" if op == "and" else "and") if negative else op,
            "left": nnf(tree["left"], negative), "right": nnf(tree["right"], negative)}


def check_operations(case: dict, tree: dict | None) -> None:
    if tree is None:
        assert case["operations"] is None
        return
    n = case["arity"]
    degrees, polynomials = [0] * n, []

    def collect(atom: dict) -> dict:
        polynomials.append(atom["terms"])
        for exponents, _ in atom["terms"]:
            for i, exponent in enumerate(exponents):
                degrees[i] = max(degrees[i], exponent)
        return atom

    map_atoms(tree, collect)
    lifted = map_atoms(tree, lambda a: dict(a, terms=[[e + [0], c] for e, c in a["terms"]]))
    drops = []
    for i, degree in enumerate(degrees):
        dropped = None if degree else map_atoms(tree, lambda a: dict(
            a, terms=[[e[:i] + e[i + 1:], c] for e, c in a["terms"]]))
        drops.append(dropped)
    assert case["operations"] == {
        "nodes": node_count(tree), "polynomials": len(polynomials),
        "support": [i for i, degree in enumerate(degrees) if degree], "degrees": degrees,
        "nnf": nnf(tree), "lift": lifted, "drops": drops}


def check_rename(case: dict) -> None:
    n, m, mapping = case["arity"], case["targetArity"], case["map"]
    assert natural(m) and len(mapping) == n
    assert all(natural(i) and i < m for i in mapping)

    def rename(atom: dict) -> dict:
        terms = []
        for exponents, coefficient in atom["terms"]:
            target = [0] * m
            for source, destination in enumerate(mapping):
                target[destination] += exponents[source]
            terms.append([target, coefficient])
        return dict(atom, terms=terms)

    source = normalize(case["body"], n)
    expected = normalize(map_atoms(source, rename), m)
    assert case["result"] == expected


def decode_dag(case: dict) -> dict:
    inputs = [normalize(p, case["arity"]) for p in case["inputs"]]
    decoded = []

    def lookup(nodes: list, index: int) -> dict:
        if not natural(index) or index >= len(nodes):
            raise ValueError("invalid node/input reference")
        return nodes[index]

    for node in case["nodes"]:
        op = node["op"]
        if op == "input":
            result = lookup(inputs, node["id"])
        elif op == "not":
            result = {"op": op, "arg": lookup(decoded, node["arg"])}
        elif op in {"and", "or"}:
            result = {"op": op, "left": lookup(decoded, node["left"]),
                      "right": lookup(decoded, node["right"])}
        else:
            result = normalize(node, case["arity"])
        decoded.append(result)
    return lookup(decoded, case["root"])


def validate(case: dict) -> None:
    assert case["schema"] == "hex-real-formula" and case["version"] == 1
    assert case["library"] == "HexRealFormula" and natural(case["arity"])
    assert len(case["freeOrder"]) == case["arity"]
    assert len(set(case["freeOrder"])) == case["arity"]
    kind = case["kind"]
    if kind == "rename":
        check_rename(case)
        return
    if kind == "prenex":
        assert all(q in {"forall", "exists"} for q in case["prefix"])
        assert len(case["binderNames"]) == len(case["prefix"])
        assert case["matrixArity"] == case["arity"] + len(case["prefix"])
        assert normalize(case["body"], case["matrixArity"]) == case["body"]
        assert case["roundTrip"] is True
        return
    try:
        if case["wireVersion"] != 1:
            raise ValueError("unsupported version")
        result = (normalize(case["body"], case["arity"]) if kind == "qf"
                  else decode_dag(case))
    except ValueError:
        result = None
    if kind == "dag":
        assert case["decoded"] == result
        assert case["dagNodes"] == len(case["nodes"])
        assert case["treeNodes"] == (None if result is None else node_count(result))
        return
    assert kind == "qf" and case["normalized"] == result
    check_operations(case, result)
    for sample in case["samples"]:
        assert len(sample["point"]) == case["arity"]
        point = []
        for numerator, denominator in sample["point"]:
            assert type(numerator) is int and natural(denominator) and denominator > 0
            q = Fraction(numerator, denominator)
            assert (q.numerator, q.denominator) == (numerator, denominator)
            point.append(q)
        expected = None if result is None else evaluate(result, point)
        assert sample["value"] == expected and sample["kernelValue"] == expected


def main() -> int:
    count = 0
    ids = set()
    for line_number, line in enumerate(sys.stdin, 1):
        case = {}
        try:
            case = json.loads(line)
            assert case["case"] not in ids, "duplicate case id"
            ids.add(case["case"])
            validate(case)
        except (AssertionError, ValueError, KeyError, TypeError, IndexError) as error:
            print(f"HexRealFormula profile=ci seed=0 line={line_number} "
                  f"case={case.get('case', '?')}: {error}\ninput={line.rstrip()}", file=sys.stderr)
            return 1
        count += 1
    if not count:
        print("HexRealFormula: empty fixture stream", file=sys.stderr)
        return 1
    print(f"HexRealFormula: {count} exact fixture checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
