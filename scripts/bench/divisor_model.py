#!/usr/bin/env python3
"""Count work in the committed family and Lean's mergeSortTR₂ recursion.

Diagnostic operation counts, never timing evidence. See the protocol for the
source correspondence and the independent lower bound from balanced splits.
"""
import json
from scripts.bench.intfactor_phase4 import DIVISOR_COUNTS, DIVISOR_PRIMES


def census(count):
    primes = DIVISOR_PRIMES[:count.bit_length() - 1]
    generated = [1]
    products = 0
    for p in reversed(primes):
        generated = [v for d in generated for v in (d, d * p)]
        products += len(generated)
    comparisons = splits = 0

    def merge(left, right):
        nonlocal comparisons
        i = j = 0
        out = []
        while i < len(left) and j < len(right):
            comparisons += 1
            if left[i] <= right[j]:
                out.append(left[i]); i += 1
            else:
                out.append(right[j]); j += 1
        return out + left[i:] + right[j:]

    def sort(values, reverse=False):
        nonlocal splits
        if len(values) < 2:
            return values
        n = len(values) // 2 if reverse else (len(values) + 1) // 2
        splits += n
        left, right = values[:n][::-1], values[n:]
        if reverse:
            return merge(sort(right, True), sort(left))
        return merge(sort(left, True), sort(right))

    result = sort(generated)
    assert result == sorted(generated)
    assert len(result) == count and len(set(result)) == count
    assert splits == count * (count.bit_length() - 1) // 2
    return dict(tau=count, subject=result[-1], generation_products=products,
                split_cells=splits, comparisons=comparisons, array_cells=count)


if __name__ == '__main__':
    print(json.dumps([census(n) for n in DIVISOR_COUNTS], indent=2))
