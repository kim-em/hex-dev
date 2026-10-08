# Sturm prerequisite performance

`HexSturm` implements shared ordered-domain Sturm–Tarski queries, exact-domain
natural root counts, prepared domains, literal certificates and checked replay.
The ordinary `HexSturmMathlib` import exports `query_iff`, root-count semantics
and certificate correctness. These APIs are usable now. The Phase-4 audit and finding dispositions are recorded below; final
attestation requires the local checks and green required CI.

The [historical report](hex-sturm-performance-history.md) preserves the original
protocols, declarations, tables and investigations. Its statements about pending
work describe those source snapshots. This report gives the current disposition;
no historical measurement or verdict is overwritten.

## Bench targets

`bench/HexSturm/Bench.lean` and `Frontend.lean` register the compiled stages,
frontends and comparators in `hexsturm_bench`. CI builds it and runs `list` and
`verify`. Fixed expected-result registrations check correctness and bitrot;
they carry no timing claim. The theorem-only companion has no benchmark
executable or dedicated performance deliverable. Its correctness and ordinary-
kernel axiom guards remain required.

| Surface / size axis | Retained evidence | Scope and disposition |
| --- | --- | --- |
| Complete query and domain checks; head degree | [Complete exact-count curves](bench-results/sturm-external-degree/README.md), [original stage results](bench-results/sturm-ec8f7c14f914/), [wide stage results](bench-results/prerequisite-sturm-head-wide/) | Competitive complete rational queries on `T_n`, degrees 4–64; stage timing claims retain their original source scope |
| Initial reduction; query degree | [Corrected bit-cost evidence](hex-sturm-performance-history.md#corrected-bit-cost-validation), [prepared query ladder](bench-results/prerequisite-prepared-query-degree/) | Fixed quadratic head and growing `X^m+1`; quadratic bit work, including literal quotient storage |
| Value-only remainder reduction | [Reduced value comparison](bench-results/sturm-reduced-value-comparison/README.md) | Avoids retaining the large quotient; complete result equality is proved; time and memory limits remain explicit |
| Prepared queries/counts, certificates, replay, transport; degree and chain length | [Thirteen short-chain families](bench-results/sturm-short-chain-degree/), [long-chain observations](bench-results/prerequisite-sturm-head-wide/) | Bounded-word linear short-chain models pass; long-chain bounds and finite-range dispositions are derived below |
| Coefficient and endpoint height, including fractional endpoints | [Growing-operand captures](bench-results/prerequisite-sturm-growing-operands/), [source/sample audit](bench-results/sturm-policy-reconciliation.json) | Thirteen complete schedules, 260 successful observations; original quadratic upper bounds are satisfied on their recorded sources |
| Integer certificate replay | [Deferred-normalization evidence](hex-sturm-performance-history.md#deferred-normalization-validation) | Proved normalization change; retained complete ladder satisfies its predeclared quartic upper bound; earlier failed models remain historical |
| Coefficient-sign primitive | [Production sign implementation and isolated comparison](bench-results/sturm-sign-comparisons/README.md) | Ordinary-kernel compiler equality removes magnitude copies; isolated stage evidence, with no complete-query speedup claim |
| Extension depth and nested coefficient evidence | [Retained consumer sweeps](sturm-downstream-evidence.md), [inherited correctness fixtures](bench-results/prerequisite-inherited-extension-evidence.json) | Actual coefficient signs through depth 12, nested-field query/replay evidence growth at depths one/two, and nested kernel observations through depth three; source-scoped consumer evidence, with full BKR/tower obligations still owned downstream |

The SPEC's conservative query bound is
`O((degree F+1)*degree P + (degree P)^3)` ring operations, excluding coefficient-
oracle costs. Integer and rational bit costs depend on operand sizes. The
[bit-cost derivations](sturm-bit-cost-models.md) and retained inventories record
chain lengths, coefficient widths, gcd/normalization work and certificate sizes;
these counts are not automatically wall-time models. Whole-child peak RSS
includes fixture preparation and is not an operation-only allocation bound.

## Verdicts

The thirteen short-chain families retain all 208 successful observations and
pass their independently derived linear models. The corrected growing-query
families pass their quadratic models. The growing-height and deferred-replay
upper bounds are one-sided observations: faster-than-bound harness results
satisfy those declarations, without becoming tight scaling laws. See the
[historical tables](hex-sturm-performance-history.md#verdicts) for the original
expressions, residuals and every retained failure.

`runSigns` maps `Int.sign` over every coefficient of every already-produced
chain. Production Tarski evaluation instead signs an endpoint value or, at
infinity, a leading coefficient (`Endpoint.signAt`, `TarskiCertificate.signs`).
It does not perform this all-coefficient traversal. The SPEC requires separate
coefficient-sign evidence but mandates no quadratic timing target for that
synthetic traversal. The `runSigns` observations measure the primitive through
this traversal; they are not an independent production-stage scaling result.
The [independent size-axis captures](bench-results/sturm-axes/) separately
record coefficient-sign timing and executed sign calls across coefficient
height, endpoint height and chain length. They predate the compiler fix and
retain their source scope. The compiler audit demonstrates the removal of
positive-integer magnitude copies. Output endpoint signing makes two calls per
chain entry, one at each endpoint; domain checks and chain construction make
additional sign calls counted by the producer/checker instrumentation. The
complete-query curves cover actual consumer queries.

The synthetic traversal is therefore an auxiliary reference with a descriptive
quadratic operation count under the current benchmarking policy. That count
does not model output-array allocation, object dispatch or memory traffic. Its
retained wide-ladder failed characterizations (+0.483310, +0.465232, +0.326483 and
+0.164190 residuals) remain
retained. The original degree-8–20 traversal passed its characterization. No new
timing-scaling pass, explanation of the wide residuals or query speedup
is claimed. Another unchanged run would settle no user-facing question and is
not scheduled. This disposition does not exempt production sign operations,
extension sign oracles or any separately mandated comparator.

The degree-128–1024 declarations have these source-based dispositions. The
[source-work derivation](sturm-readiness-work.md) covers the timed bodies,
intermediate widths, hashes and traversal costs; no schedule, expression or
original verdict is changed:

| Registration | Original expression | Retained residual | Current disposition |
| --- | --- | ---: | --- |
| `runRetarget` | `n²` | −0.431181 | Finite-range object/limb explanation; original verdict retained |
| `runPreparedCount` | `n³` | −0.698107 | Finite-range object/limb explanation; original verdict retained |
| `runEndpoints` | `n³` | −0.852720 | Finite-range object/limb explanation; proved sign replacement removes copy work |
| `runInitial` | `n²` | −0.792137 | Finite-range object/limb explanation; same-function wider ladder passes without retrospectively passing this declaration |
| `runClearing` | `n²` | −0.813471 | Finite-range object/limb explanation; same-function wider ladder passes |
| `runInteger` | `n⁴` | -1.846286 | Supported family-specific upper bound; retained schedule satisfies it |
| `runRational` | `n⁴` | -1.829867 | Supported family-specific upper bound; retained schedule satisfies it |
| `runDomain` | `n⁴` | -1.826364 | Supported family-specific upper bound; retained schedule satisfies it |
| `runChain` | `n⁴` | -1.853782 | Supported family-specific upper bound; retained schedule satisfies it |
| `runPrepared` | `n⁴` | -1.753222 | Supported family-specific upper bound; retained schedule satisfies it |
| `runCount` | `n⁴` | -1.770657 | Supported family-specific upper bound; retained schedule satisfies it |
| `runCertificate` | `n⁴` | -1.749256 | Supported family-specific upper bound; retained schedule satisfies it |
| `runPreparedCertificate` | `n⁴` | -1.729084 | Supported family-specific upper bound; retained schedule satisfies it |
| `runCountCertificate` | `n⁴` | -1.642854 | Supported family-specific upper bound; retained schedule satisfies it |
| `runFieldReplay` | `n⁴` | -1.791494 | Supported family-specific upper bound; retained schedule satisfies it |
| `runCachedReplay` | `n⁴` | -1.761928 | Supported family-specific upper bound; retained schedule satisfies it |
| `runClear` | `n⁴` | -1.825243 | Supported family-specific upper bound; retained schedule satisfies it |
| `runEmbed` | `n⁴` | -1.700830 | Supported family-specific upper bound; retained schedule satisfies it |
| `runInfinite` | `n⁴` | -1.805683 | Supported family-specific upper bound; retained schedule satisfies it |

Consecutive-degree U-chain divisions make O(n²) coefficient operations;
normalized entries and intermediate quotients/scales have O(n)-bit operands.
Classical quadratic multiplication/gcd bounds give O(n⁴) bit work, including
replay, transport and hashing. This establishes the premises of the fourteen
already-declared upper bounds; faster observations satisfy those bounds without
becoming tight timing laws. Frontend comments now state that derivation.

The five two-sided findings instead mix object visits and limb work. Source
counts predict growth between n and n² for initial reduction, clearing and
retargeting, and between n² and n³ for prepared counting and endpoint passes.
The observed downward residuals lie within the predicted one-exponent-unit
range. They retain their original verdicts; no fitted constants or new scaling
pass are claimed. Wider aliases corroborate initial/clearing behavior but do
not retrospectively pass the original declarations. These are finite-range
explanations, not claims for arbitrary inputs or enormous operands.

The [import-cone audit](bench-results/sturm-source-cone.json) records all local
compiled dependencies, toolchain and LeanBench pins since `62399ddd0`.
[All 55 selected definitions](bench-results/sturm-selected-source.json) match
that recorded source in normalized code and ordered string literals. Changed
modules add comparator/APIs, adjust proofs, or remove sign magnitude copies;
`HexPoly.Instances`' added polynomial power shortcut is not called by these
Int/Rat paths. The [head-wide snapshot check](bench-results/sturm-head-source.json)
separately verifies all twenty timed bodies against the capture’s exact saved
sources and hashes. Fifteen are identical; five read the same fixed ±2
endpoints from stored bounds instead of literals, adding constant-size conversions.
The comparison includes retargeting, embedding and all producer stages.
The measured binary is not asserted byte-identical to a current build. Dirty head-wide provenance remains a limitation; historical absolute
timings are not current-binary timings.

## Comparators

Rational and optimized integer/dyadic queries use identical mathematical inputs
and retain exact result-hash agreement. Literal transport and replay have
ordinary-kernel correspondence and conformance checks. The
[backend pairs](hex-sturm-performance-history.md#adjacent-backend-comparison)
retain every alternating adjacent arm.

The pinned FLINT qqbar and Z3 RCF comparators solve the complete exact-count
problem, including root production, open-interval filtering and sign summation.
They are orientation comparisons; their root-enumeration algorithms differ
from Hex's direct signed-remainder query. At degree 64 the recorded medians are
about 5.6 ms for Hex, 14.9 ms for Z3 and 35.3 ms for FLINT. All 40 paired counts
agree, and all 120 observations, including protocol controls, are retained.
The [size plot](bench-results/sturm-external-degree/comparison.svg) shows all
observations and their min–max ranges. No external Lean-kernel proof comparator
exists, and these curves establish no claim for arbitrary polynomial shapes or
tower coefficients.

## Profiles

The [retained representative profiles](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
provide raw perf/samply data, kernel-window sidecars, calibration, sensitivity
checks and executable hashes in persistent storage. Replay attributes 77.74%
inclusive samples to signed-chain checking; the prepared growing query
attributes 87.45% to pseudo-division. Inclusive shares overlap. These captures
explain the recorded implementations; they do not establish current absolute
timings or the validity of a timing model.

[Reprocessing the retained raw stacks](bench-results/sturm-profile-sign-attribution.json)
separates visible rational arithmetic from the coefficient-sign helper without
collecting new samples. Replay has 491/548 samples (89.60%) visibly beneath
`Rat` arithmetic and 1/548 (0.18%) beneath `Sturm.orderSign`; 56 are unassigned.
The prepared query has 486/526 (92.40%) visibly beneath rational arithmetic
and 40 unassigned, with no separately visible sign-helper sample. The
[reproduction script](bench-results/sturm-profile-sign-attribution.py.txt)
checks the raw input hashes and calibration/sensitivity diagnostics, then
forms disjoint buckets, giving sign-helper frames precedence. These are
visible-frame lower bounds: inlining and incomplete stacks prevent an exact
semantic arithmetic/sign split, and no visible sample does not prove zero
sign cost. Both captures instantiate the rational frontend; they do not
attribute integer/dyadic sign cost. The attribution concerns the recorded pre-replacement binaries.

The earlier 38 raw captures were lost after a reboot. Their summaries are
historical diagnostics only. They cannot be reprocessed or counted as retained
raw attribution. New profiling requires a concrete unresolved cost question.

## Concerns

- Large queries against a fixed quadratic still perform quadratic bit work.
  The historical quotient-retaining path reaches about 99 seconds and 32 GiB
  whole-child RSS at degree 1048576. The proved reduced value path observes
  about 137 MiB versus 2175 MiB at degree 262144 and about 78 seconds at degree
  1048576. It addresses storage, not the full arithmetic cost. Use literal
  certificate APIs when the original unreduced query must be bound.
- The finite-range explanations above do not establish tight general models.
  Original inconclusive and failed verdicts remain retained. Their scope is the
  declared families; arbitrary polynomial shapes and coefficient oracles may
  behave very differently.
- Historical dirty-tree provenance limits binary/source attribution. The new
  import-cone assessment records computational changes, but cannot reconstruct
  every unrecorded edit of the old tree. Historical numbers remain historical
  executable observations.
- The earlier raw-profile loss prevents reprocessing those captures. The later
  retained rational profiles provide visible-frame arithmetic/sign attribution,
  with explicit inlining and stack-truncation limits.
- The required extension/nested sweeps reuse the retained consumer evidence
  above. Full BKR/tower performance stays with #10377/#10378. Direct
  dependency eligibility is distinct from full transitive distribution readiness;
  HexPolyFp's concern stays with #9809.

## Verification and consumer use

The retained [local verification](bench-results/sturm-policy-verification.json)
builds all four assigned libraries and both ordinary-kernel companion targets,
passes all 93 Sturm result checks with panic rejection, and checks admission
and Mathlib-free boundaries. The [current reconciliation checks](bench-results/sturm-current-disposition-verification.json)
record the new benchmark build, 93 successful result checks and verbatim
historical-report preservation. The [reproducible token comparison](bench-results/sturm-benchmark-token-comparison.json)
checks benchmark code and string literals separately; it does not assert binary
byte identity. Compressed logs and
the freshly emitted tower fixture are [retained here](bench-results/sturm-current-disposition-verification/).
The final readiness PR requires its own green CI.

[The README](../HexSturm/README.md) gives a directly executable query/count
example. #10377, #10378 and #10575 can use the merged proved APIs while formal
phase attestation proceeds. Tower performance belongs to its existing owners;
transitive HexPolyFp readiness remains with #9809.
