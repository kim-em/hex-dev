# HexLLL Harsh-Cubic Comparator Crossover Diagnosis

## Scope

Issue #5966 asked whether the failing harsh-cubic Lean/Isabelle comparator
crossover comes from fixture construction, `GramSchmidt.Int.data` /
`scaledCoeffRows`, `LLLState` updates, exact-integer operand growth, or
benchmark registration shape.

The current gating evidence remains
`reports/bench-results/hex-lll-densified-6fcd1185cee0.json`. In that artifact,
the harsh-cubic Lean/Isabelle adjusted ratio crosses 1 at `n = 45` and reaches
`1.5821` at the largest eligible rung `n = 55`.

## Findings

The benchmark registration is measuring the intended public surface.
`Hex.LLLBench.runFirstShortVectorHarshCubicChecksum` calls
`runFirstShortVectorChecksum`, which calls
`lll.firstShortVectorUnchecked`. That entry point constructs
`LLLState.ofBasisUnchecked` from the basis and then runs `lllAux`. Precomputing
the state in `prep` would measure a different API and hide work that every
public `firstShortVector` call currently pays.

Fixture construction is not the primary gap. The harsh-cubic fixture is
deterministic and cheap relative to the failing rung: it builds an upper
triangular matrix with a diagonal scale `2^((33 * n) / 10)` and small
off-diagonal LCG perturbations. Unlike the random-bounded family, there is no
large LCG fixture-generation profile signal in the committed harsh-cubic
profile.

The committed profile in `reports/hex-lll-performance.md` already isolates the
hot path. At `n = 45`, harsh-cubic `firstShortVector` is dominated by GMP
big-integer arithmetic, and the inclusive Hex cost is led by
`Hex.lll.firstShortVector`, `runFirstShortVectorChecksum`, and
`Hex.GramSchmidt.Int.data` / `scaledCoeffRows`.

A local single-rung probe at `n = 55` compared the initial state-construction
target with the public first-short-vector target:

```text
Hex.LLLBench.runOfBasisHarshCubicChecksum          870.553 ms
Hex.LLLBench.runFirstShortVectorHarshCubicChecksum 664.614 ms
```

The exact values are noisy single-rung local measurements, but they are enough
to confirm that the failing rung is already in the same time scale as
`LLLState.ofBasisUnchecked`. The later LLL loop and result checksum are not a
separate order-of-magnitude culprit.

Comparator process overhead is also not the cause. The committed report records
steady-state Isabelle protocol overhead at about `9 us`; the failing
harsh-cubic rungs are hundreds of milliseconds.

## Conclusion

The crossover should be treated as an implementation-performance issue in the
exact-integer Gram-Schmidt construction path, specifically
`HexGramSchmidt/Int.lean`'s `gramRows`, `scaledCoeffRows`, and the no-pivot
Bareiss-shaped update surface used by `GramSchmidt.Int.data`.

No benchmark-registration change is justified by this diagnosis. The
harsh-cubic schedule and complexity model should remain unchanged until the
underlying exact-integer kernel improves and new comparator evidence is
collected.

Follow-up #5994 tracks the implementation work to reduce harsh-cubic
exact-integer Gram-Schmidt operand growth and rerun the comparator evidence.
