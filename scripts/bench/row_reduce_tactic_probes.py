#!/usr/bin/env python3
"""Generate the inverse/solve SPEC's complete seeded absolute-budget ladders."""
from fractions import Fraction
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.structural_tactic_probes import HEADER, identity, matrix, product, triangular, vector
OWNER = "HexRowReduceMathlib"
SEED = 10239
DIMENSIONS = (2, 4, 8, 16)


def inverse(a):
    n = len(a)
    work = [list(map(Fraction, row)) + list(map(Fraction, identity(n)[i])) for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if work[i][j])
        work[j], work[pivot] = work[pivot], work[j]
        scale = work[j][j]
        work[j] = [x / scale for x in work[j]]
        for i in range(n):
            if i != j:
                scale = work[i][j]
                work[i] = [x - scale * y for x, y in zip(work[i], work[j])]
    result = [row[n:] for row in work]
    assert product(a, result) == identity(n)
    assert product(result, a) == identity(n)
    return result


def transformed(n, m, rank, bits, rng, fractions=False):
    exponent = max(1, bits - max(1, rank).bit_length() - 1)
    diagonal = [rng.randrange(2 ** (exponent - 1), 2 ** exponent) for _ in range(rank)]
    denominator = 2 ** exponent + 1 if fractions else 1
    d = [[Fraction(diagonal[i], denominator) if i == j and i < rank else Fraction(0)
          for j in range(m)] for i in range(n)]
    u = triangular(n, rng, True)
    return product(product(u, d), triangular(m, rng, False)), u


def fixtures():
    cases = []

    def add(operation, family, n, bits, a, component, proposition=None, term=None, variant="", rhs=None):
        nr, nc = len(a), len(a[0])
        stem = "".join(x.title() for x in family.split("-")) + f"N{n}Bits{bits}{variant}{component.title()}"
        cases.append(dict(owner=OWNER, operation=operation, family=family, n=n, rows=nr, columns=nc,
                          configured_input_bits=bits,
                          actual_input_numerator_bits=max(abs(q.numerator).bit_length() for row in a for q in row),
                          actual_input_denominator_bits=max(q.denominator.bit_length() for row in a for q in row),
                          rhs_numerator_bits=max((abs(q.numerator).bit_length() for q in rhs or []), default=0),
                          rhs_denominator_bits=max((q.denominator.bit_length() for q in rhs or []), default=0),
                          component=component, literal_route="chain", seed=SEED,
                          module=f"{OWNER}.ProofProbe.{operation.title()}.{stem}",
                          proposition=proposition, term=term,
                          comparator_status="no-comparable-surface-in-named-comparator",
                          fresh_module_budget_ms=60_000))

    for fidx, family in enumerate(("dense-invertible", "pivot-swaps", "singular-kernel", "rational-height")):
        for n in DIMENSIONS:
            for bits in ((8, 32, 64, 256) if family == "rational-height" else (8, 32)):
                variants = ((n - 1, "AlmostFull"), (n // 2, "Half")) if family == "singular-kernel" else ((n, ""),)
                for rank, variant in variants:
                    rng = random.Random(SEED + 100000 * fidx + 1000 * n + bits + rank)
                    a, _ = transformed(n, n, rank, bits, rng, family == "rational-height")
                    if family == "pivot-swaps":
                        # Reversing a diagonal block forces swaps at every paired pivot.
                        a = [[Fraction(0) for _ in range(n)] for _ in range(n)]
                        for i in range(n):
                            a[i][n - 1 - i] = Fraction(rng.randrange(1, 2 ** (bits - 1)))
                    A = f"({matrix(a)} : Matrix (Fin {n}) (Fin {n}) ℚ)"
                    if rank < n:
                        add("inverse", family, n, bits, a, "singular", f"{A}⁻¹ = 0", variant=variant)
                    else:
                        B = matrix(inverse(a))
                        add("inverse", family, n, bits, a, "inverse", f"{A}⁻¹ = {B}")
                        add("inverse", family, n, bits, a, "product", f"{A} * {B} = 1")

    for fidx, family in enumerate(("square-unique", "tall-consistent", "wide-affine", "deficient-affine", "inconsistent-separator")):
        for n in DIMENSIONS:
            for bits in (8, 32, 128):
                nr = 2 * n if family == "tall-consistent" else n
                nc = 2 * n if family == "wide-affine" else n
                rank = n // 2 if family in ("deficient-affine", "inconsistent-separator") else n
                # The negative arm uses exactly the deficient-affine matrix.
                matrix_family = 3 if family == "inconsistent-separator" else fidx
                rng = random.Random(SEED + 1000000 + 100000 * matrix_family + 1000 * n + bits)
                a, u = transformed(nr, nc, rank, bits, rng, fractions=True)
                x = [Fraction(rng.choice((-2, -1, 1, 2)), 3) for _ in range(nc)]
                b = [sum(q * v for q, v in zip(row, x)) for row in a]
                if family == "inconsistent-separator":
                    b = [q + u[i][rank] for i, q in enumerate(b)]
                A = f"({matrix(a)} : Matrix (Fin {nr}) (Fin {nc}) ℚ)"
                rhs = vector(b)
                if family == "inconsistent-separator":
                    add("solve", family, n, bits, a, "negative", f"¬ ∃ x, {A}.mulVec x = {rhs}", rhs=b)
                else:
                    add("solve", family, n, bits, a, "residual", f"{A}.mulVec {vector(x)} = {rhs}", rhs=b)
                add("solve", family, n, bits, a, "complete", term=f"solve% {A} {rhs}", rhs=b)
    return cases


def source(case):
    text = HEADER + f"import {OWNER}.Tactic\n\n"
    text += "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
    text += "set_option profiler true\nset_option profiler.threshold 1000000\n"
    text += "set_option trace.HexMatrix.certificate true\n\n"
    if case["term"]:
        text += f"noncomputable def result := {case['term']}\n"
    else:
        text += f"theorem result : {case['proposition']} := by {case['operation']}\n"
    return text + "\n#print axioms result\n"


def main():
    cases = fixtures()
    directory = ROOT / "bench" / OWNER / "ProofProbe"
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "Baseline.lean").write_text(HEADER + f"import {OWNER}.Tactic\n")
    for case in cases:
        path = ROOT / "bench" / Path(*case["module"].split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source(case))
    manifest = [{k: v for k, v in case.items() if k not in ("proposition", "term")} for case in cases]
    (ROOT / "scripts/bench/row_reduce_tactic_probes.json").write_text(json.dumps(manifest, indent=2) + "\n")
    normalization = []
    imports = f"import {OWNER}.Tactic\nimport Mathlib.Tactic.FinCases\n"
    (directory / "NormalizationBaseline.lean").write_text(HEADER + imports)
    for case in cases:
        if case["n"] not in (2, 4) or case["configured_input_bits"] != 8:
            continue
        if case["component"] not in ("product", "residual"):
            continue
        module = case["module"] + "Normalization"
        script = ("ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]"
                  if case["component"] == "product" else
                  "ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]")
        text = HEADER + imports + "\nset_option maxHeartbeats 0\n"
        text += f"theorem result : {case['proposition']} := by\n  {script}\n\n#print axioms result\n"
        path = ROOT / "bench" / Path(*module.split(".")).with_suffix(".lean")
        path.write_text(text)
        metadata = {k: v for k, v in case.items() if k not in ("proposition", "term")}
        metadata.update(module=module, compares_to=case["module"],
                        comparator_status="entrywise-normalization-informational")
        normalization.append(metadata)
    (ROOT / "scripts/bench/row_reduce_normalization_probes.json").write_text(json.dumps(normalization, indent=2) + "\n")
    print(f"Generated {len(cases)} candidates, {len(normalization)} informational normalization probes and two baselines")


if __name__ == "__main__":
    main()
