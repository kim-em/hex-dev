# Real-algebraic performance

The shipped real subtype has a Mathlib-free benchmark executable and compiled
correctness checks. Phase 4 remains incomplete: most fixed registrations are
baseline/hash anchors, without an admissible mode or an absolute regression
budget. The forward comparison-strategy extension is excluded by the owning
SPEC; this exclusion does not waive `realCompare` or polynomial-root evidence.
The theorem-only companion has correctness and axiom tests, not its own
performance deliverable.

## Bench targets

`bench/HexRealAlgebraic/Bench.lean` registers 67 cases. `lake exe
hexrealalgebraic_bench list` lists them; `verify` checks their runtime wiring and
hashes. The existing CI job builds and verifies this executable. The retained
[local smoke-gate log](bench-results/prerequisite-verify-budget.log) records
44 Sturm and 67 real-algebraic cases, completing in 37 seconds against the
600-second operational cap. This is verification evidence, not a scientific budget.

| Shipped surface | Registrations | Evidence status |
| --- | --- | --- |
| Checked/proved constructors, casts, rational recognition | `runConstructors`, `runCasts`, `runRational` | Fixed baseline anchors |
| Arithmetic and scalar dictionaries | `runAdd`, `runSub`, `runMul`, `runDiv`, `runNeg`, `runInv`, `runNatPow`, `runIntPow`, `runScalars`; corresponding bare controls; `runHard*` | Canonical baseline and adjacent wrapper controls; mode/budget incomplete |
| Equality, comparison, order, sign, abs, conjugation | `runEquality`, `runCompare`, `runCompareExact`, `runOrder`, `runSign`, `runAbs`, `runConj`, negative/near-zero branches, `runCloseCompare`, `runCloseExact` | Fixed branch/hash/comparison anchors; separation models incomplete |
| Floor, ceiling, approximation, representation | `runRounding`, `runApprox`, `runRepr` | Baseline anchors; ceiling has proved before/after improvement |
| Square roots | `runSqrt`, `runSqrtTotal` | Baseline and branch checks; degree/height scaling incomplete |
| Polynomial constructors and root-set projections/membership | `runPolyConstructors`, `runMembership`, `runRootSet` | Mode-1 family passes |
| Polynomial roots and integer roots | `runRoots`, `runRepeatedRoots`, `runEightRoots`, `runIntegerRoots`, `runFilterRoots`, `runSortRoots`, `runExactifyRoots` | Fixed whole-path anchors, valid merge-sort family, diagnostic repeated exactification control |
| Complex norms, absolute value, real/imaginary parts | `runNorm`, `runComplexAbs`, `runProjections` | Fixed baseline/branch anchors |
| External comparison/protocol | `runQqbarCompare`, `runQqbarCloseCompare`, `runQqbarProtocol` | Informational persistent python-flint/FLINT qqbar comparison |

`runLeafChecks` does not drive the leaf problem with its array parameter.
`runExactifyRoots` repeats one fixed witness. Their harness verdicts are retained
as controls; neither establishes leaf-operation or root-exactification scaling.
`runSortRoots` measures the actual merge expression on distinct rational roots
in bit-reversal order; it only covers comparisons with disjoint stored intervals.

## Verdicts

[Array models](bench-results/prerequisite-readiness-models/arrays.json) have
four trial-major samples at each of 16,32,64,128,256. The independently derived
models are linear construction, linear absent membership, and constant tag/array
projection. Their residual slopes are about −0.115, −0.107 and 0, respectively.
[The merge-sort case](bench-results/real-algebraic-root-phases/results.json)
passes `n * (log2 n + 1)`, residual +0.062902. All are finite word-size-height
families, not general bit-complexity claims.

[The fixed canonical baseline](bench-results/real-algebraic-readiness-canonical-baseline/)
retains all four samples for all 45 anchors, including four rounding timeouts from the pre-ceiling-fix executable.
Those timeouts are retained historical observations; the optimized executable
passes current verification but has no replacement canonical baseline.
Its one-second cap is an operational safeguard, not a performance budget.
[The original baseline](bench-results/real-algebraic-readiness-baseline/)
likewise supplies coverage only.

[Hard arithmetic](bench-results/real-algebraic-hard-arithmetic/metadata.json)
uses the positive real root of `X^6−2` and `sqrt(3)`, with operands prepared
outside timed bodies. Every operation has four adjacent alternating AB/BA blocks
against the corresponding bare canonical-number operation. All 64 arms complete,
with identical hashes within every pair, and unchanged source/binary fingerprints.
The retained calibration source used the default degree/separation settings
and did not enable `expected_hash_check`. Current fixed cases have explicit
hashes and fixed degree/separation inputs;
environment variables cannot silently replace these scientific fixtures.

| Operation | Real median ms | Bare median ms | Real range ms |
| --- | --- | --- | --- |
| `Add` | 6560.009 | 6594.907 | 6486.727–6614.642 |
| `Sub` | 6512.160 | 6554.416 | 6481.416–6552.563 |
| `Mul` | 82.382 | 82.271 | 81.565–82.715 |
| `Div` | 40.273 | 40.254 | 39.962–40.466 |
| `Neg` | 26.007 | 25.953 | 25.914–26.109 |
| `Inv` | 33.120 | 32.994 | 33.030–33.688 |
| `NatPow` | 197.664 | 197.521 | 196.252–198.326 |
| `IntPow` | 244.249 | 242.489 | 243.777–245.346 |

These are calibration observations, not mode-3 passes. Parent-library attempts
can explain why isolation lacks a stable model; its lazy-add ceiling does not
cover this canonical add, which also exactifies. Its selected root can also
differ. The other operations need their own admissibility and budget justification.
No generic timeout is promoted into a scientific ceiling.

[Ceiling pairs](bench-results/real-algebraic-ceiling-pairs/) retain four adjacent
AB/BA blocks on `1 + sqrt(2)/2^50`, the same output hash in all eight arms,
frozen before/after executable hashes and the exact body snapshots. Before
medians are 408–589 ms; after medians are 9.65–15.21 µs. Non-rational ceiling
now uses floor plus one. The companion proves rational-recognition completeness,
`ceil_toReal`, `ceil_eq`, and dictionary coherence. Conformance covers either
side of ±1. This resolves the unnecessary negation in ceiling; it does not
assert general negation, inversion or rational-construction performance.

## Comparator ratios

[Separated and overlapping comparison blocks](bench-results/real-algebraic-readiness-comparisons/)
record the fixed sqrt(2)/sqrt(3) and sqrt(2)/(sqrt(2)+2^-50) inputs. Smart and
exact comparison arms are adjacent and alternate order over four blocks,
with matching ordering hashes. Median smart/exact observations are 0.420/38.991 µs
for separated inputs and 20.814/250.732 µs for overlapping inputs. These are
branch observations, not a separation-size model or a hard-case budget.

The pinned python-flint 0.9.0 / FLINT 3.6.0 public qqbar ABI has a persistent
request process; preparation is excluded, JSON transport remains timed. Its
separated/close medians are 7.451/7.436 µs; matching protocol controls are
6.375/6.358 µs. Those external arms were not adjacent to the real arm, so no
controlled AB/BA ratio or gating speed claim is inferred. A failed shift-20
fixture attempt is retained. Other compiled comparator requirements still need
reconciliation with the implemented surface and its actual matching APIs.

## Profile

[The complete profile inventory](bench-results/prerequisite-readiness-profiles/inventory.json)
records manifests, native-kernel sidecars, executable hashes, filtered summaries
and local perf/samply locations. Failed or low-confidence captures remain in
the inventory. Raw profiles are retained locally; they are not committed.
All eight canonical arithmetic captures pass the sample-count, calibration and
±5 ms sensitivity criteria.

| Canonical operation | Own % | GMP % | Allocation % | Runtime % | Samples |
| --- | --- | --- | --- | --- | --- |
| `add` | 1.49 | 31.09 | 41.63 | 18.91 | 6580 |
| `sub` | 1.41 | 30.68 | 43.23 | 18.69 | 6516 |
| `mul` | 3.34 | 16.77 | 38.31 | 37.10 | 1407 |
| `div` | 3.81 | 19.88 | 40.96 | 31.02 | 1338 |
| `neg` | 4.51 | 16.40 | 42.59 | 32.45 | 1707 |
| `inv` | 3.47 | 21.47 | 34.47 | 35.78 | 3284 |
| `natpow` | 4.49 | 16.38 | 38.64 | 35.45 | 1783 |
| `intpow` | 4.01 | 15.11 | 44.52 | 32.23 | 2197 |

Isolation dominates these calls inclusively: about 92% for addition/subtraction
and 97–99% for the other operations. The expensive exact-root-free driver,
component refinement and canonical exactification are visible in the rankings.
The corresponding bare controls show that this is underlying canonical arithmetic,
not a large real-wrapper overhead. These profiles do not supply a published
complexity theorem for that driver or a performance budget.

Canonical storage is sealed: `AlgebraicNumber.IsCanonical` requires the fixed
isolator's representative, not merely a known minimal polynomial. Thus a
reflected or reciprocal enclosure cannot be installed by discarding provenance.
Negation, inversion and nonzero rational construction still run the inherited
pipeline. Their cost is concrete and must be resolved or justified within the
owning performance audit before attestation; no unrelated parent is silently
promoted or given replacement arithmetic here.

The rational-construction anchor has 91.79% inclusive isolation and 36.67%
allocation; the real-polynomial root anchor has 96.5% isolation and about 48%
per-root exactification. Close comparison has 97.77% inclusive `realCompare`,
88.63% interval search and 82.84% refinement. Sorting and membership captures
use 32768 entries for attribution, beyond the 16–256 timing ladders; they do
not extend those scientific verdicts. The 250 ms optimized-ceiling capture
passes with 138 retained samples; its earlier kernel-region-limit failure
remains recorded. Full diagnostics, including residuals and sensitivity, are
in the linked summaries.

## Concerns

- [#10577](https://github.com/kim-em/hex-dev/issues/10577): finish operation-specific mode/budget justification and comparators, genuine root/leaf parameter families, separation/point and rounding sweeps, and square-root/rational-construction characterization. The shipped `compare_eq` and root completeness/multiplicity/sorting theorems are available independently of this timing work.

The duplicate negative-input guard in `sqrt?`/`sqrtRoot?` remains an owned
Phase-4 review concern under #10577; it does not change the proved partial result.
