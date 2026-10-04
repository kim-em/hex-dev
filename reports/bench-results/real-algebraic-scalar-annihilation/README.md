# Exact scalar size axes

[Plots](plots/scalar-comparison.svg) show all 432 completed arms. Four fixed
trial-major AB/BA blocks compare each native/comparator pair, followed by its
persistent-protocol control. Native timings include the actual shipped API and
an exact result guard. External timings include the corresponding exact
operation, result guard, JSON transport and temporary cleanup. Operands are
prepared outside timing. Add and square root do not construct an independent
expected nonrational result. Rational construction prepares its exact rational
reference; rounding checks prepared integers. Native add/sqrt guards compare
canonical polynomial arrays and sign, while external guards perform additional
exact arithmetic for annihilation and sign. Their checking costs differ and
remain timed; these curves do not isolate primitive operation costs.
Backend contexts can retain internal caches, including those populated by
warmup. These are warm API-route observations, not identical internal algorithms.

| Axis | Fixtures | Exact result guard |
| --- | --- | --- |
| Addition degree 2, 4, 8 | Positive root `a` of `X^d−2`, compute `a+1` | Native canonical polynomial `(X−1)^d−2` and positive sign; external `(result−1)^d=2` and `result>1` |
| Square-root degree 2, 4, 8 | Same `a`, compute its principal square root | Native canonical polynomial `X^(2d)−2` and positive sign; external `result²=a` and `result>1` |
| Separation exponent 4, 16, 64, 256 | Compare `√2` and `√2+2^-k` | Exact strict ordering |
| Rounding exponent 4, 16, 64, 256 | Floor/ceil of `1+√2/2^k` | Exact integers 1/2 |
| Rational coefficient bits 16, 64, 256, 1024 | Construct `((2^b−1)/3)/(2^b+1)` | Exact rational value |

The power-of-two root polynomials are Eisenstein. Their unique positive roots
make polynomial/sign and exact-annihilation/sign checks complete identities on
these fixtures. Separation and rounding keep algebraic degree two while
coefficient height also grows with `k`; they do not isolate precision from
height. Approximation requests, remaining scalar operations, representation
roundtrips and fixed-field sign still need their own characterization.
These six panels cover shipped scalar APIs, not the six forward-specified
comparison-strategy families excluded by the real-algebraic SPEC.

At degree eight native addition takes a median 322.3 ms and square root 8.840 s.
The transported FLINT medians are 24.3/15.7 µs, and Z3 RCF 19.1/23.4 µs.
These expose a severe canonical-construction/isolation gap. The
[representative square-root attribution](../readiness-runtime-profiles/README.md)
on its named source attributes 96.70% inclusive share to complex isolation.
The parent square-root API is unchanged; the wrapper's result guard in that
capture was equality with a prepared expected root, outside its setup window.
It is not a profile of every current scalar wrapper or family.

At separation exponent 256 native comparison takes 47.0 µs. Native floor and
ceiling take about 3.0 µs. Framing overhead dominates these fast external arms;
raw timings cannot rank their primitive performance. The protocol curves are
shown separately, without subtraction. The Z3 RCF adapter has no matching
floor/ceil API, and supplies no rounding comparison.

At 1024 coefficient bits native rational construction takes about 1.496 ms,
versus transported FLINT/Z3 observations of 15.1/39.7 µs. This is construction,
not the direct `toRat?` recognition fast path. The latter's
[large-height evidence](../real-algebraic-rational-height-after-sqrt/)
separately measures the operation after canonical preparation.

All guards match and no arms are capped, discarded or rerun. Metadata records
source `a3ddc9473f`, immutable source snapshots, native executable SHA-256,
CPU 45, host/load context and every command. Both computational source and
binary remain unchanged across collection. Dependencies are pinned to
python-flint 0.9.0 / FLINT 3.6.0 and z3-solver 4.15.4.0. Reproduce with
`scripts/bench/real_algebraic_scaling_comparison.py` and
`scripts/plots/real-algebraic-readiness.py`.

[Earlier expected-root controls](../real-algebraic-scalar-expected-root-controls/)
remain separate, with every failed/capped arm retained. This descriptive
comparison is not a cost-model verdict, fixed-budget admission or Phase-4
attestation. No phase counter is promoted.
