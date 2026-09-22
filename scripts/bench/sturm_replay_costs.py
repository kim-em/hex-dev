#!/usr/bin/env python3
"""Untimed operation volumes for the actual Chebyshev replay certificates.

Check the scale formulas against retained production certificates. Count the
schoolbook multiplication upper bound, not GMP instructions or wall time.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.sturm_bit_costs import primitive_u  # noqa: E402


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def step(k: int, first: bool = False) -> list:
    a = 2 * (k - v2(k + 1))
    b = a + v2(k + 1) if first else a + 1 + v2(k + 1) - v2(k + 2)
    c = a + v2(k) if first else a + v2(k) - v2(k + 2)
    return [1 << a, [[0, 1 << b], 1 << c]]


def volumes(terms: list[tuple[int, list[int]]]) -> tuple[int, int]:
    bits = products = 0
    for scalar, coefficients in terms:
        bits += sum(abs(x).bit_length() for x in coefficients)
        products += ((scalar.bit_length() + 63) // 64) * sum(
            (abs(x).bit_length() + 63) // 64 for x in coefficients)
    return bits, products


def main() -> None:
    fixtures = ROOT / 'reports/bench-results/sturm-ec8f7c14f914/fixtures.jsonl'
    for line in fixtures.read_text().splitlines():
        row = json.loads(line)
        if row['family'] == 'head-degree':
            n = row['parameter']
            assert row['certificate']['remainders']['steps'] == [
                step(k, k == n - 1) for k in range(n - 1, 0, -1)]
    print(json.dumps({'all_retained_head_step_formulas': True}))
    total_bits = total_products = eval_bits = final_scans = 0
    previous, current = primitive_u(0), primitive_u(1)
    for k in range(1, 2048):
        following = primitive_u(k + 1)
        a, (q, c) = step(k)
        bits, products = volumes([(a, following), (q[1], current), (c, previous)])
        total_bits += bits
        total_products += products
        acc = 0
        for coefficient in reversed(current):
            acc = coefficient + 2 * acc
            eval_bits += abs(acc).bit_length()
        final_scans += v2(abs(acc))
        assert v2(abs(acc)) == (1 if k % 2 else 0)
        if k + 1 in (128, 256, 512, 1024, 2048):
            # Replace the hypothetical U_{k+1} first step by the actual T_{k+1}.
            head = [0] + [x * (1 << v2(k + 1)) for x in current]
            for j, coefficient in enumerate(previous):
                head[j] -= coefficient * (1 << v2(k))
            aa, (qq, cc) = step(k, first=True)
            first_bits, first_products = volumes([
                (aa, head), (qq[1], current), (cc, previous)])
            print(json.dumps({
                'degree': k + 1,
                'recurrence_operand_bits': total_bits - bits + first_bits,
                'schoolbook_limb_products': total_products - products + first_products,
                'tail_horner_accumulator_bits': eval_bits,
                'tail_final_normalization_iterations': final_scans,
            }), flush=True)
        previous, current = current, following


if __name__ == '__main__':
    main()
