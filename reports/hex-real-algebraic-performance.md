# Real-algebraic performance

The implemented real-algebraic API has compiled benchmark registrations,
exact external comparisons, practical size plots, retained profiles and
ordinary-kernel correspondence. This report gives the Phase-4 coverage decision
for that surface. The [historical report](hex-real-algebraic-performance-history.md)
preserves the original declarations, failures, measurements and source-scoped
investigations verbatim. Final attestation requires local checks and green CI.

The forward comparison-strategy extension at the end of the shared SPEC's
[Exact comparison strategies](../SPEC/Libraries/hex-real-algebraic.md#exact-comparison-strategies)
is excluded. Its new Tarski/approximation algorithms and six comparator
families are not implemented obligations of the shipped owners. The implemented
`realCompare`, `signField` and `RealAlgebraicPoly.roots` remain in scope.

## Bench targets

`bench/HexRealAlgebraic/Bench.lean` registers 196 cases in
`hexrealalgebraic_bench`. CI builds it and runs `list` and panic-rejecting
`verify`. Scientific evidence below uses the same actual APIs, with the stated
preparation, result-guard and source boundaries. Fixed hash-only cases check
correctness and bitrot; they carry no performance verdict.

The theorem-only Mathlib companion has no dedicated performance deliverable.
Its ordinary-kernel correctness, public correspondence and axiom guards remain
required. No benchmark executable imports Mathlib.

## Declared input families

Coverage follows the current policy's judgment rule. The seven audited
families have these dispositions; the decision is about useful evidence for
actual operations, not a quota of separately timed public functions.

| Family | Evidence | Coverage decision and limits |
| --- | --- | --- |
| Canonical real arithmetic | [Actual scalar degree curves](bench-results/real-algebraic-scalar-annihilation/README.md), [parent-isolation reuse](bench-results/canonical-parent-isolation-reuse/README.md), [hard wrapper/bare controls](bench-results/real-algebraic-hard-arithmetic/) | Addition and square root cover operand degrees 2/4/8; canonical add/mul/powers retain adjacent observations and equality proofs. Arithmetic delegates to Phase-7 HexNumberField plus one reality check. Slow isolation is explained; no universal degree/height scaling law is asserted. More independent negation/inversion/norm microbenchmarks would not resolve a demonstrated wrapper defect. |
| Real order and rounding | [Separated/overlapping smart/exact pairs](bench-results/real-algebraic-readiness-comparisons/), [separation and near-integer curves](bench-results/real-algebraic-scalar-annihilation/README.md) | Actual comparison and floor/ceil cover separation exponents 4/16/64/256. Approximation is an inherited bounded-precision operation with checked correspondence; no new wrapper algorithm or measured bottleneck calls for a separate precision campaign. Close-root and higher-degree limits remain. |
| Rational height | [Recognition/floor/ceil ladders](bench-results/real-algebraic-rational-height-after-sqrt/README.md) | Predeclared models pass through two million bits after the proved square-root initializer fix. Canonical preparation is excluded and still costly. Its diagnostic is retained; another recognition profile would explain no outstanding failure. |
| Polynomial arrays and sorting | [Array families](bench-results/prerequisite-readiness-models/arrays.json), [sort results](bench-results/real-algebraic-root-phases/results.json) | Coefficient construction, absent membership and projections pass; distinct rational-root sorting passes n(log₂ n+1). Fixed-leaf/exactification repetitions remain controls, not growing leaf-size evidence. General expensive comparisons are covered by order/scalar evidence, not inferred from this rational sort. |
| Real polynomial roots | [Implemented API comparisons](bench-results/real-algebraic-poly-roots-comparison-after/README.md), [nonreal rejection](bench-results/real-algebraic-root-rejection-pairs/README.md), [shared isolation](bench-results/real-root-isolation-reuse/README.md) | Actual rational-coefficient degrees 2/4/8 and quadratic-coefficient degrees 1/2/4 retain complete fingerprints and time/memory observations. Higher local probes and exact conformance supplement correctness, not the scientific ladder. The remaining isolation cost is documented below. No general high-degree performance claim is made. |
| Representation | Fixed formatter registration; ordinary generated-term roundtrip checks; [local proof/representation observations](hex-real-algebraic-performance-history.md#profile) | Repr delegates to the inherited canonical formatter. Ordinary-kernel roundtrip correctness remains required. Generated-expression elaboration is not a computational wrapper scaling claim; larger manual observations remain separate from CI. There is no assigned tactic or proof generator requiring a new proof-track timing campaign here. |
| Fixed-field sign | Current complete `runFieldSign` vector and companion guards; [coordinate-size comparison](../bench-results/field-sign/README.md), [common-field consumer comparison](../bench-results/field-sign/common-fields/README.md) | `signField` delegates to Phase-7 `QAdjoin.signApprox` with the generator's reality proof. Historical coordinate ladders concern the pre-refactoring implementation; the consumer comparison includes the later per-call reality check. Neither is relabelled as current per-call scaling evidence. There is no new algorithm, dispatch policy or unexplained wrapper cost demanding another ladder. New comparative algorithms remain excluded. |

## Verdicts

Passing array, sorting and rational-height schedules retain their original
expressions and all samples. Scalar and root comparisons are representative
observations, with variable-cost inventories: eliminant construction,
factorization, precision/separation-driven isolation, canonical exactification,
root filtering and sorting, plus output guards. They make no fitted timing-law
claim. Counts of field operations alone cannot model the variable isolation
and factorization work.

Concrete avoidable work has been corrected with complete ordinary-kernel
API equalities: nonreal roots are rejected before exactification; certified
parent isolation arrays are reused during canonical arithmetic/conversion;
real entries sharing an irreducible parent share isolation; rational
recognition constructs the already-normalized core rational directly; ceiling
avoids needless canonical negation; the prime planner's square-root seed is
bounded by bit length. All failed prototypes, operational caps and inconclusive
comparisons remain retained. The successful fixes do not retrospectively pass
withdrawn models or erase earlier observations.

### Direct polynomial-root size comparisons

The [latest root plots](bench-results/real-root-isolation-reuse/plots/roots-comparison.svg)
show all corrected native observations and source-scoped external references.
Four adjacent alternating before/after blocks per fixture retain 48 arms;
preparation and warmup are excluded, solving/filtering/exactification/sorting
and native result guards remain timed. Degree-eight rational enumeration costs
about 93.6 ms; quadratic-coefficient degree four costs about 96.5 ms. Paired
median improvements on applicable fixtures are 1.27–1.56×. The singleton
control is approximately unchanged; the quadratic-degree-two individual pairs
include one regression. Whole-child RSS is about 67 MiB, including preparation.

The retained FLINT/Z3 references are not contemporaneous paired arms for this
latest implementation. Larger native fixtures remain roughly 800–2,700 times
those historical external medians. Backend root representation, guards,
transport and internal algorithms differ. This is a serious optimization
opportunity, not a newly invented parity requirement. The old 2.9× regressing
function-valued cache and its explanatory profile remain retained separately.

### Rational recognition and leaf height

[Height plots](bench-results/real-algebraic-rational-height-after-sqrt/plots/rational-height.svg)
cover recognition, floor, ceiling and the former quotient control after
canonical preparation. The direct-recognition theorem preserves exactly the
former rational result. Preparation costs are a separate observation and are
not hidden inside a claimed fast construction path. Large rational arithmetic
keeps canonical degree one, with correctness cases including denominator 2^100.

## Scalar size axes

[The degree plots](bench-results/canonical-parent-isolation-reuse/plots/scalar-comparison.svg)
show every measured point and min–max range, together with historical FLINT/Z3
reference curves. Parent reuse reduces scalar addition by 1.91–2.01× and
square root by 1.14–1.27× on degrees 2/4/8. The retained `630a40345b` degree-eight
addition costs about 160 ms; square root costs about 7.1 seconds and produces
a degree-16 canonical number. This is unsuitable for repeated interactive
square-root calls at that rung. Isolation/refinement explains that recorded cost. Later merged
[#10804](https://github.com/kim-em/hex-dev/pull/10804) adds direct selected-root
certification before the global isolation fallback. The old 7.1-second value
is not a measurement of that changed implementation, and no current speedup
is inferred. Canonical exactification still inherits its parent-library costs. No claim of uniformly fast arbitrary canonical arithmetic is made.

[The separation/rounding plots](bench-results/real-algebraic-scalar-annihilation/plots/scalar-comparison.svg)
cover actual smart comparison and near-integer rounding. At exponent 256,
recorded comparison costs about 47 µs and floor/ceil about 3 µs. Those leaf
bodies are unchanged by the later isolation-sharing fixes. Degrees and
coefficient heights of these comparisons are not independently varied.
External framing dominates the fastest arms, so primitive rankings are not
inferred from their raw times.

## Comparator ratios

The registered external comparators are informational FLINT real-qqbar exact
comparison/polynomial roots and Z3 RCF polynomial roots. They are implemented
on the common domains above. All 48 original native/external root pairs and
all 432 scalar collection arms complete with matching exact guards/hashes;
controls and earlier failed expected-root attempts remain retained. Native
polynomial/sign guards and external annihilation/sign guards differ and remain
timed. Preparation is excluded; external JSON and temporary cleanup are timed.

Smart versus exact native comparisons agree on the separated/overlapping
inputs. Rational sorting only exercises disjoint-interval comparisons. The
Z3 adapter has no matching rounding API; no Z3 floor/ceil ratio is claimed.
The inherited fixed-field comparisons have their own source and end-to-end
boundaries. No external system supplies a comparable Lean-kernel proof surface.
The excluded extension's comparator families are not asserted implemented.

## Profiles

The [parent-reuse square-root profile](bench-results/canonical-parent-isolation-reuse/README.md)
retains 812 calibrated kernel-window samples, with confidence and sensitivity
checks: 95.32% inclusive isolation, 39.90% common-field presentation and
20.81% powers. Shares overlap and are not added. The root-cache prototype
profile explains its rejected regression, not the final binary's distribution.
Earlier root/addition profiles retain their measured source scope. Root reuse
changes the filtering stage, but the separately merged direct selected-root
certification changes the canonical arithmetic selection path. The old profile
is historical attribution, not a current distribution or proof that all
recorded redundant isolation persists.

The earlier 38 raw captures were lost after a reboot. Their saved summaries are
historical diagnostics and cannot be reprocessed. Later raw captures and
frozen binaries have persistent storage and hash inventories. No blanket
profile refresh is needed; a new profile should answer an unexplained result.

The [latest root benchmark import-cone comparison](bench-results/real-algebraic-root-source-cone.json)
finds all 304 local modules unchanged between the measured `4ea36ac633` source
and the readiness base `90c4f0e144`, with unchanged toolchain and LeanBench pin.
The [older scalar comparison](bench-results/real-algebraic-scalar-source-cone.json)
records intervening computational changes, including selected-root certification,
guarded Hensel products and restored fast polynomial imports. Older scalar
curves/profiles retain historical scope. They are reused to identify variable
costs and document observed limits, not to assert current absolute times or
binary identity. No source change is concealed by a blanket unchanged-path claim.

## Concerns

- Canonical high-degree arithmetic remains expensive. In particular, the
  retained pre-direct-certification degree-eight square root takes seconds.
  This is a source-scoped warning, not a current timeout claim. Use the small-degree API
  with these limits in mind; repeated canonicalization is a poor hot path.
  Fixed-field/tower consumers have separate owners and evidence requirements.
- Root enumeration remains much slower than FLINT/Z3 on the tested inputs,
  although the corrected small-degree calls complete in milliseconds. Larger
  degrees, heights, close-root separations and precision requests have no
  general practical-performance attestation here. Old caps remain historical;
  passing later probes are correctness observations, not scaling passes.
- Real-root sharing still performs 2k+1 parent factorizations for an irreducible
  group of k real entries, versus 2k previously. Existing exact selector checks
  remain. Another reuse optimization is possible, but this report asserts no
  general speedup or measured factorization bottleneck for that extra call.
- Rational canonical preparation remains more expensive than recognition.
  Whole-child memory observations include preparation and are not allocation
  bounds for the individual operation.
- Profiles and comparator observations are source scoped; lost captures and
  dirty-tree evidence do not acquire stronger provenance through this audit.
  Final CI is an operational gate, not a portable timing budget.

These are supported implementation limits and optimization opportunities.
After the identified redundant-work defects are fixed, the current policy does
not require unrestricted fast canonical isolation, external speed parity or
a benchmark/profile for every wrapper to attest the implemented surface.
No outstanding declared timing finding or mandated comparator is waived by
that coverage decision.

## Verification

The four library targets, both ordinary companion test targets, computational
conformance and semantic kernel tests build. The local real-algebraic emitter
and pinned exact FLINT oracle pass all 92 cases with zero unavailable-component
skips. Admission checks reject nonstandard axioms, `sorryAx` and `native_decide`.
Panic-rejecting benchmark verification and the Mathlib-free check are required,
as is green CI on the final PR head. The [readiness audit](real-closure-prerequisites.md)
records the direct dependency checks and consumer guidance. This attestation
covers development APIs, not split-repository publication.
