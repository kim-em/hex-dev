# Joint and interacting-coefficient work

The diagnostics use the actual BKR, descriptor completion and common-product
comparison constructors, with the existing rational and rational-function
coefficient fields. Their local arithmetic observers preserve every value;
`keep_eq` proves this independently of the observer Boolean. No coefficient
field instance or query kernel is replaced.

## Interacting infinitesimals

The input is the existing conformance family P=X²−g² and queries [X−g,X−a],
where g=ε₁−ε₁²−ε₂−…−ε_d. At depth one a=ε₁; otherwise a is the preceding
generator. The two roots have signs (−,−) and (0,−), each with count one.
The Z3 RCF oracle independently checks the actual coefficient arrays,
polynomials, interval and complete answer, at depths one through three.
Ordinary unobserved replay checks the intended subjects in all three modes.

| Depth | Reduced outer calls | Direct outer calls | Reference outer calls | Maximum normalized rational bits (reduced/direct/reference) | Maximum rational coordinate slots |
| ---: | ---: | ---: | ---: | --- | ---: |
| 1 | 1387 | 1240 | 852 | 5 / 5 / 7 | 14 |
| 2 | 1387 | 1240 | 852 | 8 / 8 / 9 | 80 |
| 3 | 1387 | 1240 | 852 | 9 / 9 / 10 | 250 |

These are outer coefficient operands/results, including preparation and the
builders' checks. They exclude internal temporaries and operations inside the
recursive field dictionaries, numeral constructors and equality tests. Division
has zero observed outer calls; the other seven operation categories occur.
Constant outer counts do not imply constant arithmetic cost as depth grows.

### Denominator-one fast paths

`RationalFn.normalizeWith` returns `ofPoly p` directly when q=1, instead of
computing a gcd, two exact quotients and normalization scales.
`RationalFn.cancelWith` returns common factor 1 and cofactors p and 1 in the
same case. Existing reconstruction, monicity and coprimality proofs check
these branches. General denominators continue through the existing algorithm.
Nested polynomial coefficients encounter these branches at successive levels;
removing their recursive gcd/division work is a concrete change to computation.

A short LeanBench comparison uses identical fixed callbacks at depths one and
two. Each callback includes preparation, reduced/direct/reference construction,
ordinary replay and coefficient encoding. Arithmetic observation is disabled.
There are six adjacent pairs per case, alternating AB/BA in trial-major order,
pinned to one automatically leased CPU on the shared host. Every completed
sample and export is retained in [the paired archive](data/sign-det-operand-work/paired/metadata.json).
No scaling exponent or tolerance is fitted.

| Depth | Baseline median | Fast-path median | Median within-pair baseline/fast ratio |
| ---: | ---: | ---: | ---: |
| 1 | 22.34 ms | 5.80 ms | 3.86 |
| 2 | 531.54 ms | 27.47 ms | 19.41 |

All 24 fixed observations succeed and share the same answer hash per case.
These are host-specific observations of these callbacks, not a universal
nested-field speedup or a depth-complexity theorem. They do not time Lean proofs.

The earlier [interacting conformance run](sign-det-nested-fields.md) took about
442 seconds across four depths. The current full emitter, including its
invalid-evidence checks, takes about 0.55 seconds across the same four inputs,
with all independent Z3 checks passing. These executions use different source
snapshots; their quotient is not a controlled speedup claim. The controlled
comparison above isolates the two fast paths against the same diagnostic code.
Depth four is a small functional check, not a repeated deep timing ladder.
The remaining recursive numeral-construction cost in the scalar-sign family
is separate; this change does not remove it or establish `tower8` integration.

## Joint comparison operands

For odd n the original descriptors select 1 from Xⁿ−1 and −1 from Xⁿ+1.
The diagnostic validates both sources, completes them, then performs the
actual common-product comparison. FLINT independently checks the supplied
heads, the monic gcd 1 represented by the native factor −2, and the common
head (1−X²ⁿ)/2; exact derivative evaluation identifies
the two roots and full derivative signs. Ordinary unobserved replay checks
both joint tables, descriptors, common product and order.

| n | Outer coefficient/sign calls | Maximum normalized rational bits | Source-derived binary-operation temporary bound |
| ---: | ---: | ---: | ---: |
| 3 | 114523 | 9 | 19 |
| 7 | 807761 | 36 | 73 |
| 15 | 5662908 | 107 | 215 |

The operation bounds are 2B+1 for normalized operand/result maximum B.
They cover coefficient integers in ordinary binary rational arithmetic, not
backend scratch storage or fixed rational/integer matrix kernels. The pipeline
includes source construction/completion outside the separately timed comparison
callback, so its counters must not be called that callback's isolated counts.

One successful `CommonProduct.build` performs one explicit polynomial gcd and
three explicit `DensePoly.divMod` calls. It checks four product identities.
The gcd of the two binomial heads reaches the nonzero constant −2; divisions
inside gcd, signed remainder chains and moment reduction are separate work.
These are source-call counts for common-product construction, not a count of
all integer normalizations or remainder calculations in the pipeline.

## Reproduction and scope

Build the three diagnostic executables:

```sh
lake build hexsigndet_interacting_trace hexsigndet_interacting_bench hexsigndet_arithmetic_trace
```

Run the interacting trace and
`hexsigndet_arithmetic_trace --joint`; check their emitted subjects with
`scripts/bench/sign_det_operand_work.py interacting|joint OUTPUT`.
The independent checks require the pinned Z3 RCF and python-flint.

The archive retains raw observations, source patches over an immutable main
base, separate source/build bindings for both timing binaries, diagnostic
binary hashes, compiler/toolchain bindings and the paired collector. The
recorded runtime Git environment describes the collector checkout; the
explicit build bindings describe the binaries. Source reconstruction retains
the measured file bytes, including the trailing blank line removed from the
current trace module.
Early exploratory records remain separate and establish no scientific timing
verdict. A stored witness maximum is not a temporary-operand maximum; neither
kind of bit count alone is a wall-time law. No general gcd-growth theorem,
internal nested-field peak or downstream tower-depth limit is asserted.
