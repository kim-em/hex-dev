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
took 32 seconds on that historical 67-case source and exceeded the 30-second per-library soft threshold.
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
for about 26 of the 32 local seconds in the recorded 72-case check on
`eabbeea9f`; the current 102-case CI log has no per-case timing breakdown. There is no repeat-count or tuning setting
left to reduce for these calls. The harness policy forbids replacing a
canonical fixed input with an easier smoke input, and the scientific inputs
and their expected hashes are preserved. The operational warning and remaining
canonical-arithmetic cost remain under #10577. The full CI cap remains enforced;
no increase or verification bypass is introduced. The retained 336-second run
had only 24 seconds of headroom; the 349-second run had 11, and the
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

## Declared input families

The manifest declares seven shipped input families. Declarations identify the
coverage obligation; they do not certify completed evidence or advance Phase 4.
The separately forward-specified comparison-strategy extension remains excluded.

| Manifest family | Current evidence | Remaining evidence or concern |
| --- | --- | --- |
| `canonical-real-arithmetic` | Compiled scalar/constructor, complex norm/absolute-value and real/imaginary projection anchors, canonical hard arithmetic and matching bare-parent controls; retained representative addition profile | Operation-specific characterization and remaining raw profile coverage; parent isolation cost |
| `real-order-and-rounding` | Equality/sign/abs/conjugation/min-max anchors, separated and overlapping compare anchors, near-zero/near-integer checks, approximation and square-root anchors; proved ceiling improvement | Genuine separation, precision and degree/height families, current attribution and scientific characterization |
| `rational-height` | Declared direct degree-one recognition/floor/ceil/control ladders; exact construction/recognition guards and retained preparation diagnostic | Canonical preparation prerequisite prevents current scientific observations; the isolated parent proposal is not applied |
| `polynomial-arrays-and-sorting` | Passing coefficient-array, membership/projection and distinct rational-root sorting families | Representative raw profile retention; repeated fixed-leaf/exactification controls do not establish varying leaf-size coverage |
| `real-polynomial-roots` | Actual rational/quadratic-coefficient root API degree comparisons, complete fingerprints, repeated/integer/filter roots and multiplicity/exactification anchors, retained rejection pairs and before/after profiles | Severe remaining canonical isolation cost and higher-degree characterization |
| `representation` | Fixed Repr formatter anchor and generated-term ordinary-kernel roundtrip checks | Separately reported growing-size roundtrip performance and attribution; formatter-only timings do not discharge this obligation |
| `fixed-field-sign` | Current complete compiled sign vectors and companion guards; inherited source-scoped comparisons | Current operation-specific scaling and retained profile coverage; no new Tarski/approximation algorithm is assigned here |

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
The [post-change larger probes](bench-results/real-algebraic-poly-roots-probes-after/README.md)
both pass within the 60-second operational cap, in about 9.3–9.4 seconds
including preparation. They verify rational degree 16 and quadratic degree 8,
but do not extend the operation-only scientific timing ladder.

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
uses the same canonical input and complete result. The [post-initializer collection](bench-results/real-algebraic-rational-height-after-sqrt/)
records current two-sided passes for direct recognition and floor at 262144,
524288, 1048576 and 2097152 coefficient bits, with four trials per rung.
Residual slopes are +0.015245 and −0.013195. At two million bits their median
operation times are 57.990 and 24.644 µs. Ceiling and former-quotient control
observations remain required; these results establish no controlled improvement
ratio. Canonical input preparation remains expensive and is excluded from the
operation timer.

The first rung's [preparation diagnostic](bench-results/real-algebraic-rational-height/direct/preparation-diagnostic/README.md)
produced no timed observation and was terminated after 969.496897 seconds.
The native worker backtrace places it in the factorization prime planner's
coefficient-norm square root in HexArith. Both completed perf attachments and
the exact executable are retained persistently, including their failed Lean
caller unwinding. They are preparation diagnostics, not operation-only profile
attribution. The diagnostic invoked `_child` directly, bypassing parent
supervision. Ordinary `run` caps the entire child, including preparation,
through `LeanBench.spawnWithCap` at `maxSecondsPerCall` plus `killGraceMs`.
That historical diagnostic predates the proved bit-length square-root
initializer now used by `HexArith.Nat.floorSqrt`. Supervised scientific
recognition and floor runs on the changed source now complete and pass, as
reported above. The remaining ceiling/control evidence and canonical input
construction cost remain concerns. The historical prerequisite diagnostic is
recorded on [#10577](https://github.com/kim-em/hex-dev/issues/10577#issuecomment-5971054259);
it is distinct from HexPolyFp's #9809 concerns. No transitive implementation or
phase metadata is changed by this evidence.

## Scalar size axes

The [current scalar comparison](bench-results/real-algebraic-scalar-annihilation/README.md)
retains 432 adjacent native/FLINT/Z3/protocol arms on arithmetic-degree,
rational-construction-height, close-comparison and near-integer-rounding axes.
All exact result guards pass, with no cap, filtering or unchanged rerun. The
[plots](bench-results/real-algebraic-scalar-annihilation/plots/scalar-comparison.svg)
show all observations and spreads; protocol curves remain separate.

Native arithmetic checks canonical minimal polynomial and sign; external
arithmetic checks exact annihilation and sign. No expected algebraic root is
prepared. Contexts can retain caches populated by warmup. Addition and square
root on the positive root of `X^8−2` take median 322.3 ms and 8.840 seconds,
versus transported FLINT/Z3 observations in the tens of microseconds. This
is a severe unresolved canonical-construction/isolation gap. These descriptive
API-route ratios do not supply a speed gate or Phase-4 budget.

At separation exponent 256 native comparison takes 47.0 µs; floor and ceiling
of `1+√2/2^k` take about 3.0 µs. The external framing control dominates these
fast references, so raw ratios cannot rank primitive performance. The Z3 RCF
adapter supplies no matching floor/ceil API. The axes keep algebraic degree
fixed while coefficient height also grows with separation exponent.

The [earlier expected-root controls](bench-results/real-algebraic-scalar-expected-root-controls/)
remain archived, including capped attempts and their distinct warm-context
boundary. The [boundary diagnostic](bench-results/scalar-sqrt8-boundary/) shows
why those whole-child caps cannot be operation-only lower bounds. The
[retained square-root attribution](bench-results/readiness-runtime-profiles/README.md)
identifies isolation on its named source and result-guard wrapper; the parent
square-root API is unchanged. This is not a blanket profile attestation.

These panels measure the implemented scalar APIs. They do not reopen the
excluded forward comparison-strategy extension or attest its six comparator
families. Remaining scalar operations, approximation, representation roundtrip
and fixed-field sign require their own evidence.

## Comparator ratios

The manifest classifies `FLINT real-qqbar exact comparisons and polynomial roots`
and `Z3 RCF real polynomial roots` as informational. Both are wired for the
actual root fixtures; the pinned FLINT comparison driver additionally covers
separated and overlapping values. External root fingerprints infer their
minimal-polynomial field from the Eisenstein fixture, while the native API
constructs its canonical representation. Sorting, exact external annihilation,
transport and cleanup remain timed. These are bounded API-route comparisons,
not identical internal algorithms or a global speed requirement. The scalar
collection adds addition, square root, rational construction and comparison
for both backends, and exact FLINT floor/ceil. Remaining scalar operations and
other matching surfaces still need characterization.

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

[Current polynomial-root attribution](bench-results/prerequisite-current-root-profile-d6cebc4de/rational-roots.manifest.json)
profiles `Hex.RealAlgebraicBench.runRationalRoots8`, parameter 0, on source
`d6cebc4de` and automatically leased CPU 28. Its 1266 kernel-window samples
pass calibration (0.903 ms residual), confidence and ±5 ms sensitivity checks.
Isolation has 94.47% inclusive share. Leaf costs are allocation 40.21%, GMP
23.62%, Lean runtime 28.28%, own code 2.76% and other 5.13%. Exactification and
component norm-root selection have 62.48% and 31.60% inclusive shares;
these inclusive figures are not added. The raw perf/samply data, sidecar,
source snapshots, executed collector and exact executable remain in the
persistent location recorded by the manifest. The [summary](bench-results/prerequisite-current-root-profile-d6cebc4de/rational-roots.summary.json)
identifies the dominant refinement and Taylor work. This supplies current
attribution for the rational-coefficient `X^8 - 2` family member; it does not
establish
operation-specific scientific admission or a portable budget.

[Historical representative attribution](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
on clean source `62399ddd0` has 6592 kernel-window samples for canonical hard
addition. Calibration residual is 0.046 ms, and sample-count and ±5 ms
sensitivity checks pass. Root isolation has 91.88% inclusive share, refinement
90.61%, and allocation 42.38% self share. Raw perf/samply data, kernel sidecars,
symbols and checksums are retained in persistent storage. This retains attribution for its recorded source before certified parent
isolation reuse; it supplies no current-operation budget or replacement for
completed timing samples. The parent-reuse capture below supplies canonical-addition attribution on
`08c8a9f13e`; its executable hash `8626a68c…` matches the `d6cebc4de` root
capture exactly.

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

On the historical inventory source, the rational-construction anchor has
91.79% inclusive isolation and 36.67%
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
  remain diagnostics and cannot be reprocessed. The replacement `62399ddd0`
  addition capture is historical after parent reuse; the `08c8a9f13e` addition
  and `d6cebc4de` rational-root captures supply retained attribution for their
  scoped implementations without a blanket rerun of completed evidence.

- [#10577](https://github.com/kim-em/hex-dev/issues/10577): finish operation-specific mode/budget justification and comparators, genuine root/leaf parameter families, separation/point and rounding sweeps, and square-root/rational-construction characterization. The shipped `compare_eq` and root completeness/multiplicity/sorting theorems are available independently of this timing work.

- [The precise #10577 prerequisite diagnostic](https://github.com/kim-em/hex-dev/issues/10577#issuecomment-5971054259)
  records excessive canonical rational preparation through HexArith's
  bit-length-sensitive square-root initialization and degree-one factorization
  in `HexNumberField/Roots.lean` / `Convert.lean`. Related square-root work
  [#721](https://github.com/kim-em/hex-dev/issues/721) is closed. The proved bit-length initializer is implemented, with an ordinary-kernel
  equality to Lean core square root and large-square conformance. Its selective
  Hex-only factorization refresh retains all 392 inputs and reuses every external
  comparator record. Recognition and floor now pass their declared height
  models; ceiling/control evidence and costly degree-one canonical construction
  remain. No unrelated phase metadata is promoted.

The checked square-root wrapper delegates directly to `sqrtRoot?`, removing
the duplicate negative-input check. Existing selector soundness and nonnegative
totality prove the same contract. Earlier square-root baseline observations
retain their pre-change source; they provide no current performance admission.

[Required CI for merged #10684](bench-results/prerequisite-required-ci-77a844987.json)
passes all 91 Sturm and 102 real-algebraic result checks at 63/360 seconds,
including 61 seconds for this executable. Its full library/conformance/manual
builds, architecture/trust/ordinary-kernel checks and all 83 exact real-algebraic
oracle cases pass with no unavailable-component skips. The fresh rebased local
[local record on `89bed`](bench-results/prerequisite-root-rejection-head-verification.json)
separately measures 32 seconds for this executable. The earlier
[39-second pre-rebase observation on `ca1f80de4`](bench-results/prerequisite-root-rejection-local-verification.json)
remains retained on its named source.

[The extra all-library run](bench-results/prerequisite-full-ci-77a844987.json)
completes every result check across 57 executables but fails the unchanged
operational cap at 388/360 seconds. This executable takes 64 seconds; GF2,
Roots and PolyZGcd take 47, 46 and 44 respectively. That extra run was cancelled
after its completed benchmark failure while the remaining all-library oracle step
was still running, to retrieve its diagnostic log. It supplies no full-oracle
success claim; the owned oracles pass in the filtered required run. The cap
failure recurs across this assignment's retained
[366/360](bench-results/prerequisite-required-ci-273ee7ef4.json),
[384/360](bench-results/prerequisite-required-ci-82039231f.json) and 388/360 runs.
No completed same-base main breakdown establishes causal attribution. These
failures are operational observations, not failed result checks or Phase-4
verdicts. The [single unchanged operational recheck of source `77a844987`](bench-results/prerequisite-full-ci-recheck-77a844987.json)
also completes every result check across 57 executables but fails at 382/360
seconds, including 62 seconds for this executable. Its remaining all-library
oracle step was cancelled after that completed failure; no full-oracle pass
is claimed and no further unchanged recheck is performed.

On the recorded 72-case source `eabbeea9f`, hard addition/subtraction and their
bare controls account for about 26 of 32 local seconds. The current CI warning
has no per-case breakdown. The [retained hard-add profile](bench-results/prerequisite-representative-profiles-62399ddd0/real-hard-add.summary.json)
on `62399ddd0` locates three near-equal isolation passes before certified
reuse: lazy eliminant selection, factor
exactification, and canonical representative construction. In particular,
`exactFactor?` in `HexNumberField/Convert.lean` and `rawRep?` in
`HexNumberField/Basic.lean` run the same deterministic factor isolation at the
same separation depth on that recorded source. The certified reuse below
removes the canonical-construction re-isolation while preserving the complete
canonical result; the eliminant and candidate runs remain separate.

The profiled `Convert.lean`, `Basic.lean`, `Lazy.lean` and real-add paths are
unchanged from `62399ddd0` through the measured root-rejection source. The
near-equal terminal-path shares use tail-call attribution: `ofNormalized?` is
the tail call of `exactFactor?`, so those displayed shares are not nested
inclusive totals. Arbitrary inclusive profile shares must not be added.

[Certified candidate-isolation reuse](bench-results/number-field-isolation-reuse/README.md)
removes the canonical-construction re-isolation from `exactFactor?`, with
whole-Option equality preserving the same stored representations. Four
adjacent AB/BA pairs on `7ceaf9d47d` measure hard addition/subtraction about
1.5 times faster. The six actual root-API degree rungs retain 48 successful
arms; their [size plot](bench-results/number-field-isolation-reuse/roots-comparison.png)
shows an improvement but a severe remaining gap to retained external
references. The external lines are historical observations, not fresh pairs
with these native samples. A [current representative profile](bench-results/number-field-isolation-reuse/profile/hard-add.summary.json)
on `08c8a9f13e` retains 4344 kernel samples with calibration/count/sensitivity
checks passing. Isolation remains 90.56% inclusive, with the remaining lazy
eliminant and candidate-exactification paths separately visible at 45.26%
and 45.35%; these are tail-call attributions, not arbitrary additive
inclusive totals. All raw artifacts persist at the manifest paths.
The local normal-form migration, fixed-presentation conversion reuse and
per-root enumeration reuse remain outside this targeted repair. No phase
counter or general CI headroom assertion follows.

[PR CI for #10695 (head `d6cebc4de`, test merge `252f17576`)](bench-results/prerequisite-required-ci-d6cebc4de.json)
passes all 57 executable checks (2828 benchmark cases) at 284/360 seconds on
`d6cebc4de`, including 32 seconds for real-algebraic verification. Every
conformance oracle passes, including the 83 exact real-algebraic cases with
zero unavailable-component skips, together with library/conformance/manual,
architecture, trust and axiom checks. The source's unchanged 360-second cap
passed. Later main cap changes in #10696 (`52ef27c0be`, 600 seconds)
are outside this tested source. This is one pass on one runner; it does not
establish headroom under 360 seconds on slower runners. The soft 30-second
warning remains for real-algebraic (32 seconds), GF2 (41), Roots (37) and
PolyZGcd (35); those warnings are retained in the CI record.
The [local full smoke](bench-results/prerequisite-full-local-smoke-d6cebc4de.json)
passes the same 57 executables at 150/360 seconds on its recorded host, with
joint degree-three and ECM continuation checks also passing. The three initial
local dependency failures remain retained. These are operational observations,
not controlled comparisons with earlier GitHub runs or scientific Phase-4
admission. All four assigned phase counters remain 3.
