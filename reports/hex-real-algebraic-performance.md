# Real-algebraic performance

The shipped real subtype has a Mathlib-free benchmark executable and compiled
correctness checks. Phase 4 remains incomplete: most fixed registrations are
baseline/hash anchors, without an admissible mode or an absolute regression
budget. The forward comparison-strategy extension is excluded by the owning
SPEC; this exclusion does not waive `realCompare` or polynomial-root evidence.
The theorem-only companion has correctness and axiom tests, not its own
performance deliverable.

## Bench targets

`bench/HexRealAlgebraic/Bench.lean` registers 102 cases. `lake exe
hexrealalgebraic_bench list` lists them; `verify` checks their runtime wiring and
hashes. The existing CI job builds and verifies this executable. The retained
[local verification log](bench-results/prerequisite-verify-budget.log) records
44 Sturm and 67 real-algebraic cases, completing in 37 seconds against the
600-second local script default; CI sets a 360-second cap. The real executable
took 32 seconds and exceeded the 30-second per-library soft threshold.
The subsequent [direct-recognition verification](bench-results/prerequisite-direct-recognition-verification.json)
records all 71 current real cases and 44 Sturm cases passing, with 129 validated
Sturm coefficient fixtures; it measures only the owned executables, not the
repo-wide CI budget.
[Required CI](https://github.com/kim-em/hex-dev/actions/runs/36972953823)
records 60 seconds for this executable and 336 seconds total under the shared
360-second cap. The later pre-rebase [required CI](https://github.com/kim-em/hex-dev/actions/runs/36983780557)
records 36 seconds for this executable and 217 seconds total under the same cap.
These are historical verification observations on their recorded sources, not
scientific budgets or current-base headroom assertions. The rebased verification
is recorded separately in [the rebase evidence](bench-results/prerequisite-rebase-verification.json).

The merged [required CI on `9c298eb98`](https://github.com/kim-em/hex-dev/actions/runs/37171438363)
passes all required gates, including the 71 Sturm and 72 real-algebraic cases,
at 33/360 seconds for the owner-filtered benchmark gate. This records #10660,
before the new direct polynomial-root registrations and early-rejection change;
it does not establish main's all-library headroom or attest changed source.

[Completed CI on `62399ddd0`](bench-results/prerequisite-required-ci-62399ddd0.json)
passes all required checks, including the exact oracles. Benchmark verification
uses 349 of 360 seconds, with 63 seconds for this executable and only 11 seconds
of total headroom. This observation precedes the conversion/API rebase onto
`c74bc64a0`; it does not attest the rebased source or establish stable headroom.

[Merged required CI on `4a028ba84`](bench-results/prerequisite-required-ci-4a028ba84.json)
passes every required check, including the conformance/factorization tail.
Verification uses exactly 360 of 360 seconds, with 62 seconds for the real
executable and no measured total headroom. This attests the Phase-3 PR #10580,
not the subsequent direct-recognition/headline/benchmark changes. The unchanged
cap remains a gate; neither a portable timing budget nor stable headroom is
inferred from the completed pass.

[Required CI on `273ee7ef4`](bench-results/prerequisite-required-ci-273ee7ef4.json)
passes the builds and conformance/oracle gates and every owned result/hash
check, but fails the repo-wide smoke cap at 366/360 seconds. Its real executable
takes 62 seconds and Sturm takes 2. The complete failed run and all 57
per-library durations remain retained. This is an operational gate failure,
not a scientific scaling verdict; the final revision still requires green CI.

[Current-base local checks](bench-results/prerequisite-followup-current-base-verification.json)
pass all 72 real cases, including fixed-field sign, and all 71 Sturm cases.
Their two-executable total is 36 seconds, with 32 for real and 4 for Sturm;
this is not the repo-wide required CI gate.

The fixed verifier already invokes each runner once in-process, without warmup
or tuning. The hard add/subtract registrations and their bare controls account
for about 26 of the 32 local seconds. There is no repeat-count or tuning setting
left to reduce for these calls. The harness policy forbids replacing a
canonical fixed input with an easier smoke input, and the scientific inputs
and their expected hashes are preserved. The operational warning and remaining
canonical-arithmetic cost remain under #10577. The full CI cap remains enforced;
no increase or verification bypass is introduced. The retained 336-second run
had only 24 seconds of headroom; the 349-second run had 11, and the latest
  completed required run on `4a028ba84` has none.
Shared-host and CI variance remain concerns, and required CI must pass on the
final source without weakening the cap.

| Shipped surface | Registrations | Evidence status |
| --- | --- | --- |
| Checked/proved constructors, casts, rational recognition | `runConstructors`, `runCasts`, `runRational` | Fixed baseline anchors |
| Arithmetic and scalar dictionaries | `runAdd`, `runSub`, `runMul`, `runDiv`, `runNeg`, `runInv`, `runNatPow`, `runIntPow`, `runScalars`; corresponding bare controls; `runHard*` | Canonical baseline and adjacent wrapper controls; mode/budget incomplete |
| Equality, comparison, order, sign, abs, conjugation | `runEquality`, `runCompare`, `runCompareExact`, `runOrder`, `runSign`, `runAbs`, `runConj`, `runCloseCompare`, `runCloseExact` | Fixed branch/hash/comparison anchors; separation models incomplete |
| Fixed-field coordinate sign | `runFieldSign` | Complete result vector on constant and nonconstant paths in the positive square-root-of-two embedding. [Inherited owner evidence](../bench-results/field-sign/README.md) concerns a pre-refactoring executable; current operation-specific mode/budget remains required |
| Rational degree-one leaf height | `runRationalRecognition`, `runRationalFloor`, `runRationalCeil`, `runRationalQuotient` | Independently derived mode-1 candidates; first-rung canonical preparation exceeds the declared operational cap; no current admission |
| Floor, ceiling, approximation, representation | `runRounding`, `runApprox`, `runRepr` | Baseline anchors; ceiling has proved before/after improvement |
| Square roots | `runSqrt`, `runSqrtTotal` | Baseline/branch checks on pre-change source; degree/height scaling incomplete |
| Polynomial constructors and root-set projections/membership | `runPolyConstructors`, `runMembership`, `runRootSet` | Mode-1 family passes |
| Polynomial roots and integer roots | `runRoots`, `runRepeatedRoots`, `runEightRoots`, `runIntegerRoots`, `runFilterRoots`, `runSortRoots`, `runExactifyRoots`; direct `runRationalRoots*` and `runQuadraticRoots*` plus FLINT/Z3 controls | Direct implemented `RealAlgebraicPoly.roots` coverage and exact external degree comparisons; canonical enumeration performance remains a concern |
| Complex norms, absolute value, real/imaginary parts | `runNorm`, `runComplexAbs`, `runProjections` | Fixed baseline/branch anchors |
| External comparison/protocol | `runQqbarCompare`, `runQqbarCloseCompare`, `runQqbarProtocol` | Informational persistent python-flint/FLINT qqbar comparison |

`runLeafChecks` does not drive the leaf problem with its array parameter.
`runExactifyRoots` repeats one fixed witness. Their harness verdicts are retained
as controls; neither establishes leaf-operation or root-exactification scaling.
`runSortRoots` measures the actual merge expression on distinct rational roots
in bit-reversal order; it only covers comparisons with disjoint stored intervals.

## Verdicts

### Direct polynomial-root size comparisons

The earlier root-set filtering and integer-root anchors did not directly time
`RealAlgebraicPoly.roots`. Six native registrations now exercise that actual
API, with 24 external/protocol registrations. They solve `X^n−2` at degrees
2, 4 and 8 and `X^n−√2` at degrees 1, 2 and 4. Coefficient height is fixed;
degree one returns one root and the even degrees return two. Complete ordered
minimal-polynomial/sign/multiplicity fingerprints identify every output root
on these Eisenstein fixtures. This does not waive general root correspondence.

The [current size comparison](bench-results/real-algebraic-poly-roots-comparison-after/README.md)
retains all 144 successful observations, comprising 48 adjacent native/external
pairs and 48 protocol controls. Prepared inputs and child warmup are excluded;
native solving, exactification, filtering and sorting remain timed. The pinned
FLINT qqbar and Z3 RCF backends solve the same exact root problem, with sorting,
annihilation checks, JSON and temporary cleanup timed. Their minimal polynomial
is inferred from the fixture, not extracted from internal representations.
All complete-result guards and paired hashes match; source/binary fingerprints
remain unchanged. The [earlier source-scoped comparison](bench-results/real-algebraic-poly-roots-comparison/README.md)
and every failed [operational probe](bench-results/real-algebraic-poly-roots-probes/README.md)
remain retained. Old cap failures do not assert a timeout on the changed code.

| Fixture | Hex median ms (Z3 pairs) | Z3 RCF median ms | FLINT qqbar median ms | Median adjacent Hex/Z3 ratio |
| --- | ---: | ---: | ---: | ---: |
| Rational degree 2 | 3.837 | 0.0295 | 0.0365 | 127.96 |
| Rational degree 4 | 18.215 | 0.0342 | 0.0549 | 537.24 |
| Rational degree 8 | 245.314 | 0.0407 | 0.0973 | 6016.01 |
| Quadratic degree 1 | 9.352 | 0.0161 | 0.0218 | 579.59 |
| Quadratic degree 2 | 24.850 | 0.0311 | 0.0625 | 799.94 |
| Quadratic degree 4 | 253.621 | 0.0364 | 0.1170 | 6905.61 |

FLINT pairs have their own native medians in the CSV. Ratios are medians of
adjacent pairs, not ratios of aggregate medians. Raw and protocol-adjusted
curves appear in the [PNG](bench-results/real-algebraic-poly-roots-comparison-after/comparison.png),
[SVG](bench-results/real-algebraic-poly-roots-comparison-after/comparison.svg)
and [PDF](bench-results/real-algebraic-poly-roots-comparison-after/comparison.pdf).
Protocol cost is material on the smallest external rungs; both curves are
displayed without claiming isolated backend-algorithm timings. All timing dots
and observed min–max shading are retained. No fitted complexity model or
invented portable budget is needed to see the severe comparative gap.

The owned `ofRoot?` now rejects nonreal refined isolations before exactification.
The companion proves exact API equality `ofRoot?_eq`, with an ordinary-kernel
axiom guard; completeness and multiplicity proofs reuse it. The controlled
[adjacent frozen-executable pairs](bench-results/real-algebraic-root-rejection-pairs/README.md)
retain all 16 successful arms with identical complete results: median adjacent
before/after ratios are 3.412 for rational degree 8 and 2.248 for quadratic
degree 4. This resolves avoidable canonicalization of nonreal roots.
The [current representative attribution](bench-results/real-algebraic-poly-roots-profiles-after/README.md)
still places about 96% inclusive cost in isolation and 76% in canonical
exactification. The retained real roots repeat their parent canonical isolation;
this remaining algorithmic cost is unresolved. Earlier profiles remain valid
only on their named pre-change source. No phase counter is advanced.

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
and did not enable `expected_hash_check`. The observed full-result hashes
match the current fixed expected hashes (for example `Add-0-Hard.log` and
`runHardAdd` both give `0x7cc18faa80303c8`), supporting fixture identity. Current fixed cases have explicit
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

### Rational recognition and leaf height

`toRat?` constructs a core `Rat` directly from the canonical primitive linear
polynomial. Erased positivity and coprimality proofs replace normalization
through a quotient. `toRat?_formula` proves equality with the former expression;
the companion's existing soundness and completeness contract remains guarded
by ordinary-kernel axiom tests. Higher-degree inputs still return `none`.

The [historical height family](bench-results/real-algebraic-rational-height/)
retains all 72 initial points and their three inconclusive verdicts. The
[larger-height observations](bench-results/real-algebraic-rational-height/higher/)
retain 48 points: former recognition and floor pass their declared linear
models, while ceiling remains inconclusive. These observations describe the
former quotient implementation, not the direct constructor. Its retained
[diagnostic recognition profile](bench-results/real-algebraic-rational-height/real-rational-recognition.manifest.json)
identifies GMP normalization work; neither it nor the former timings admits
the changed implementation.

The new [premeasurement derivation](bench-results/real-algebraic-rational-height/direct/derivation.md)
accounts for the pinned runtime's integer-negation copy and structural output
hash. The family keeps degree one, grows coefficient height, and approaches
1/3. Recognition, rational floor, rational ceiling and the former-quotient
comparison control have independently derived linear models. The control
uses the same canonical input and complete result. No controlled improvement
ratio or current scaling verdict has been obtained.

The first rung's [preparation diagnostic](bench-results/real-algebraic-rational-height/direct/preparation-diagnostic/README.md)
produced no timed observation and was terminated after 969.496897 seconds.
The native worker backtrace places it in the factorization prime planner's
coefficient-norm square root in HexArith. Both completed perf attachments and
the exact executable are retained persistently, including their failed Lean
caller unwinding. They are preparation diagnostics, not operation-only profile
attribution. The diagnostic invoked `_child` directly, bypassing parent
supervision. Ordinary `run` caps the entire child, including preparation,
through `LeanBench.spawnWithCap` at `maxSecondsPerCall` plus `killGraceMs`.
No supervised scientific run was attempted; the four-rung declaration remains
unmeasured and unadmitted. This prerequisite
concern is recorded on [#10577](https://github.com/kim-em/hex-dev/issues/10577#issuecomment-5971054259);
it is distinct from HexPolyFp's #9809 concerns. No transitive implementation or
phase metadata is changed by this evidence.

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

[Retained representative attribution](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
on clean source `62399ddd0` has 6592 kernel-window samples for canonical hard
addition. Calibration residual is 0.046 ms, and sample-count and ±5 ms
sensitivity checks pass. Root isolation has 91.88% inclusive share, refinement
90.61%, and allocation 42.38% self share. Raw perf/samply data, kernel sidecars,
symbols and checksums are retained in persistent storage. This supplies the
required representative attribution, not an operation-specific budget or a
replacement for the completed timing samples below.

[The complete profile inventory](bench-results/prerequisite-readiness-profiles/inventory.json)
records manifests, native-kernel sidecars, executable hashes, filtered summaries
and local perf/samply locations. Failed or low-confidence captures remain in
the inventory. [The artifact check](bench-results/prerequisite-profile-availability.json)
finds all 38 raw capture directories unavailable at their recorded local paths.
The committed manifests, summaries and diagnostics remain intact; their raw
perf/samply files are not committed and cannot currently be reprocessed.
The recorded diagnostics for all eight canonical arithmetic captures pass the
sample-count, calibration and ±5 ms sensitivity criteria. These historical
summaries do not establish complete Phase-4 raw-artifact retention.

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

- Actual canonical real-polynomial root enumeration remains several thousand
  times slower than the exact external root backends on the larger tested
  rungs, after the proved early nonreal rejection. Repeated canonical isolation
  remains dominant. Higher-degree characterization and operation-specific
  Phase-4 admission remain incomplete; the historical oversized cap failures
  are retained without claiming they reproduce on changed source.

- The earlier 38 raw captures were lost after a reboot. Their saved summaries
  remain diagnostics and cannot be reprocessed; the new representative capture
  supplies retained attribution without a blanket rerun of completed evidence.

- [#10577](https://github.com/kim-em/hex-dev/issues/10577): finish operation-specific mode/budget justification and comparators, genuine root/leaf parameter families, separation/point and rounding sweeps, and square-root/rational-construction characterization. The shipped `compare_eq` and root completeness/multiplicity/sorting theorems are available independently of this timing work.

- [The precise #10577 prerequisite diagnostic](https://github.com/kim-em/hex-dev/issues/10577#issuecomment-5971054259)
  records excessive canonical rational preparation through HexArith's
  bit-length-sensitive square-root initialization and degree-one factorization
  in `HexNumberField/Roots.lean` / `Convert.lean`. Related square-root work
  [#721](https://github.com/kim-em/hex-dev/issues/721) is closed. The isolated
  proved initializer proposal is outside this PR pending scope agreement;
  rational-height declarations remain unadmitted, and no unrelated phase
  metadata is changed.

The checked square-root wrapper delegates directly to `sqrtRoot?`, removing
the duplicate negative-input check. Existing selector soundness and nonnegative
totality prove the same contract. Earlier square-root baseline observations
retain their pre-change source; they provide no current performance admission.

The 32-second per-library verification warning remains under #10577; the
360-second CI cap is an operational safeguard. Hard addition/subtraction
and their bare controls account for most of the warning.
