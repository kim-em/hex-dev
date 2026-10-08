# Sturm and real-algebraic prerequisite readiness

Scope: [#10577](https://github.com/kim-em/hex-dev/issues/10577), the implemented
HexSturm and HexRealAlgebraic pairs. Phase eligibility is checked against direct
`libraries.yml` dependencies. This is a monorepo readiness audit, not a release
or distribution attestation.

All four record Phases 1–3. Phase 1 reuses the implemented APIs; Phase 2 has
independent per-library scaffolding reviews in `status/`. Phase 3 has compiled
operation/property/edge checks for both cores, ordinary-kernel companion builds
and axiom guards. Required CI on the final revision must pass before merge.
Phase 4 remains incomplete for both cores;
the theorem-only companions need their cores at Phase 4. Their named
headlines are available from the ordinary companion libraries.

Performance priorities follow actual consumer operations. The retained
[complete Sturm-query degree comparisons](bench-results/sturm-external-degree/README.md)
show competitive rational-query times on degrees 4–64. The bench-local
all-coefficient sign traversal is an isolated diagnostic; its paired improvement
does not establish a query or tactic speedup. Its inconclusive characterization
needs an evidence-based disposition under the current policy, alongside the
SPEC's separately required production coefficient-sign coverage.
The actual real-polynomial root curves expose a much larger user-facing cost.
[Certified isolation sharing](bench-results/real-root-isolation-reuse/README.md)
improves the measured enumeration fixtures by 1.28–1.56× where reuse applies,
while retaining both the rejected prototype and the severe external gap.

| Library | Implemented/proved coverage | Phase requirements still to discharge | Evidence |
| --- | --- | --- | --- |
| HexSturm | Shared ordered-domain kernel; guarded queries and exact-domain natural counts; prepared domains, retargeting, counts, cached replay, literal certificate transport and a proved remainder-only value query | Phase 4: comparator/registration reconciliation, admissible characterization and retained concerns | `HexSturm/Basic.lean`, `Transport.lean`, `conformance/HexSturm/Conformance.lean`, [performance report](hex-sturm-performance.md) |
| HexSturmMathlib | Domain equivalence, prepared bindings, producer acceptance, representation congruence and rational/integer whole-Option agreement; exact query iff, count equality and bounds in the ordinary companion and public umbrella | Phase 4: core eligibility; no dedicated performance deliverable for this theorem-only layer | `Domain`, `Compare`, `Rational`, `DenominatorClearing`, `IntCast`; `HexSturmMathlib/Soundness.lean`; ordinary-kernel `HexSturmMathlibTests` |
| HexRealAlgebraic | Real subtype, rational recognition and toRat?-first rounding, canonical arithmetic/order, rounding, square roots, fixed-field coordinate signs, integer and algebraic-coefficient real roots, complex norms; proved early nonreal rejection and actual polynomial-root degree comparisons | Phase 4: canonical root enumeration and canonical scalar addition/square root remain far behind external backends; remaining isolation cost and higher-degree characterization remain; fixed hash checks carry no performance claim | `conformance/HexRealAlgebraic`, pinned FLINT/qqbar oracle and fixtures; `bench/HexRealAlgebraic/Bench.lean`; [root curves and attribution](hex-real-algebraic-performance.md#direct-polynomial-root-size-comparisons) |
| HexRealAlgebraicMathlib | Arithmetic/order and closure, law/dictionary coherence, rational recognition, rounding, approximation, Repr round trip, fixed-field sign correspondence, combined roots contract and real closedness | Phase 4: core eligibility; no dedicated performance deliverable for this theorem-only layer | `HexRealAlgebraicMathlib/Instances.lean`, `Roots.lean`, `RealClosed.lean`, `HexRealAlgebraicMathlib/Tests.lean` |

## Semantic availability

`HexRealRootsMathlib` builds the shared root-sum foundation, and the ordinary
`HexSturmMathlib` umbrella exposes the frontend semantics. `HexQuerySemantics`
retains semantic regression tests and the remaining owners’ adapters. `HexSturmMathlib.query_sound` and `check_sound` do not require
roots to lie in the coefficient field. `rootCount_isSome` preserves precisely
the query domain; `query_nonneg`, `rootCount_query` and `rootCount_map` justify
`Int.toNat` on every lawful query-one result. Arbitrary supplied sign functions
are subject to the theorem's lawful interpretation hypotheses. No negative
query-one result is accepted under those hypotheses.

`AlgebraicNumber.realCompare_eq` and `realCompareExact_eq` are already proved
in `HexNumberFieldMathlib/Nearest.lean`; the subtype's `compare_eq` consumes
them. `RealAlgebraicPoly.contains_roots_iff`, `roots_all_iff`,
`roots_multiplicity` and `roots_sorted` prove the required real-polynomial
contracts, including zero's universal root set. The new ordinary-kernel axiom
guards check the dependencies of these named correspondence theorems.

Main's merged [#10641](https://github.com/kim-em/hex-dev/pull/10641) also supplies
`RealAlgebraicNumber.signField` and its `signField_spec` / `signField_eq`
correspondence. The existing computational field-sign conformance and companion
axiom guards remain registered after the rebase. Its [retained comparison](../bench-results/field-sign/README.md)
identifies the measured pre-refactoring source and explicitly supplies no
current-call scaling check; it does not close the four-library Phase-4 gaps.

RealAlgebraicNumber operations remain independent of HexSturm, HexSignDet and
HexRealClosure. Rational recognition uses the canonical linear polynomial;
conformance cases retain degree one through arithmetic, including zero
and a denominator of 2^100. `toRat?_formula` proves that constructing the
recognized rational directly from primitive coefficients preserves the former
quotient result. The existing companion recognition contract is unchanged.

The forward comparison-strategy extension at the end of
[Exact comparison strategies](../SPEC/Libraries/hex-real-algebraic.md#exact-comparison-strategies)
is excluded: point/lazy/fixed-field/tower algorithms and the six new comparator
families are not shipped obligations under this audit. This exclusion does
not exempt the implemented `realCompare` or `RealAlgebraicPoly.roots` surface.

## Headline correctness and bridge boundary

`PLAN/Conventions.md` requires a named end-to-end headline correctness theorem
in the Mathlib bridge for Phase-4 attestation. The existing correspondence
results compose into the named headlines `HexSturmMathlib.query_iff` and
`Hex.RealAlgebraicPoly.roots_spec`. Their SPECs state the semantic clauses and
the independently required public contracts for prepared queries, supplied
certificates, scalar operations and representation changes. Ordinary-kernel
guards admit only the three standard logical axioms; a noninjective-storage
query instantiation also builds without field or order instances on storage.
Both headlines build in their ordinary companion targets. Shared
`TarskiFoundation` / `TarskiSoundness` and the integer specialization live in
HexRealRootsMathlib; frontend `Soundness` lives in HexSturmMathlib and is
exported by `import HexSturmMathlib`. The dependency and trusted-import checks
cover this integration. This removes the monorepo API gap without recording
Phase 4 or claiming split-package publication. The companion replay tests
still import the
conformance fixture module `HexSturm.Fixtures`; split-package test wiring must
provide it when those libraries are published. Available mathematical proofs do not depend on that
publication work.

## Dependencies and downstream owners

HexSturm's direct prerequisites are HexPoly (7) and HexRealRoots (7).
HexSturmMathlib also requires HexPolyMathlib and HexRealRootsMathlib (both 7).
HexRealAlgebraic requires HexNumberField (7); its companion also requires
HexNumberFieldMathlib and HexRealRootsMathlib (both 7). Each pair must advance
core before companion at dependency-coupled phases.

[#10377](https://github.com/kim-em/hex-dev/issues/10377) and
[#10378](https://github.com/kim-em/hex-dev/issues/10378) can consume the proved
monorepo APIs immediately. Their BKR, extension-depth, nested-evidence and tower
performance obligations are separate. [#10352](https://github.com/kim-em/hex-dev/issues/10352)
owns rank readiness. [#10575](https://github.com/kim-em/hex-dev/issues/10575) owns
integration/publication of the semantic adapters and the package-boundary audit.
The unchanged downstream [infinitesimal integration evidence](bench-results/prerequisite-inherited-extension-evidence.json)
supplies the corrected de Moura–Passmore counts 3 and 2, and third-derivative
query zero on the positive interval. Its current source/fixture hashes also
match the retained four-depth local native conformance record. Required CI
checks the 31-case infinitesimal corpus and depths one and two. These are
correctness fixtures; extension-depth and lower-level kernel sign-evidence
performance remain separate requirements.
The transitive HexPolyFp performance concerns belong to
[#9809](https://github.com/kim-em/hex-dev/issues/9809); no unrelated counter is
promoted by this assignment.

The rational-height benchmark exposed expensive canonical preparation through
HexArith's square root for the factorization prime planner. The proved
bit-length initializer now preserves `Nat.sqrt` exactly, and the selective
Hex-only factor sweep has current source-bound evidence. [The retained height
captures](bench-results/real-algebraic-rational-height-after-sqrt/README.md)
admit the registered recognition, floor, ceiling and former quotient control
operation timers through two million bits on their recorded source. Canonical
preparation remains costly and is excluded from those timers; profiles are
needed for unexplained costs, not automatically for every registered operation. No unrelated library phase is promoted. Historical failed
preparation evidence is retained with its original source and scope.

## Verification

Local Lake builds pass for all four libraries and `HexQuerySemantics`.
The expanded real-algebraic conformance module and `HexRealAlgebraicMathlibTests`
compile. [The direct-recognition verification](bench-results/prerequisite-direct-recognition-verification.json)
records a full default build, full conformance build, semantic headline guards
and its 71 real / 44 Sturm benchmark smoke cases. [Merged-base follow-up checks](bench-results/prerequisite-followup-merged-base-verification.json)
cover the recorded 71 cases in each executable, both ordinary-kernel companion
test targets and the new short-chain and external-query registrations.
[Current-base verification](bench-results/prerequisite-followup-current-base-verification.json)
covers the 71 Sturm and 72 real-algebraic cases, including `signField`, on
base `4f8745e64`. The full default build has 15803 jobs; the admission scan
covers 284 import cones and 1062 local modules. Persistent rechecks match all
168 representative-profile artifacts and all four exact-binary entries.
The axiom guards admit exactly `propext`, `Classical.choice`, and
`Quot.sound`; no new axiom, admission or native_decide is introduced.
The Mathlib-free benchmark target compiles and all shipped-API verification cases pass.
[Retained fixed-case baseline observations](bench-results/real-algebraic-readiness-baseline/results.json)
are fixed correctness observations; their 30-second operational caps are
safeguards and supply no scientific performance claim. Independent review tokens are present; compiled conformance and the pinned
83-case core and 92-case local exact oracles pass with no skipped operations.
[The earlier rebase verification record](bench-results/prerequisite-rebase-verification.json)
retains checks and failed runs on its recorded bases, including inherited
field-sign conformance and ordinary-kernel axiom guards.
[The conversion/API rebase verification](bench-results/prerequisite-conversion-rebase-verification.json)
identifies checks on base `c74bc64a0`, including both companion test targets.
The square-root simplification has 83 fresh exact-oracle cases with zero skips;
fresh fixtures match the committed file byte for byte. [Required CI for the merged
Phase-3 PR #10580](bench-results/prerequisite-required-ci-4a028ba84.json)
passes on its recorded source, using exactly 360 seconds of the 360-second
benchmark-verification cap. It does not attest the follow-up changes; their
required CI must pass separately without weakening that cap. The follow-up
[required CI on `273ee7ef4`](bench-results/prerequisite-required-ci-273ee7ef4.json)
passes every owned result/hash check but fails the repo-wide smoke cap at
366/360 seconds. Its completed run and per-library breakdown remain retained.
[The raw-artifact availability check](bench-results/prerequisite-profile-availability.json)
finds 38 prerequisite-readiness capture directories unavailable at their recorded
local paths. Committed manifests, summaries, diagnostics and completed timing
samples remain retained. [Retained representative captures](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
now supply replay, prepared-query and canonical-addition attribution with raw
perf/samply data, kernel sidecars and 126 matching artifact checksums in
persistent storage. They pass calibration and sensitivity checks; they do not
replace completed measurements or admit unresolved complexity models.
The [real-algebraic performance report](hex-real-algebraic-performance.md) and
the Sturm report distinguish valid family passes from failed hypotheses,
controls and fixed observations without budgets. Phase 4 remains incomplete.

[Required CI for merged #10684](bench-results/prerequisite-required-ci-77a844987.json)
attests the proved early nonreal rejection and expanded direct benchmark
surface on `77a844987`: 91 Sturm and 102 real-algebraic checks, 63/360 filtered
seconds, 83 exact real-algebraic oracle cases without unavailable-component
skips, and full library/conformance/manual/architecture/trust checks.
[The separately retained all-library run](bench-results/prerequisite-full-ci-77a844987.json)
completes all 57 executable result checks but fails the unchanged total cap at
388/360 seconds; its remaining all-library oracle step was cancelled after that
completed failure, so no full-oracle success or headroom is claimed. The owned
oracles pass separately in required filtered CI; no completed same-base main
breakdown establishes causal attribution for the recurring cap failures. The
manifest now declares the real-algebraic comparator and input-family coverage
obligations with their actual pending evidence. These declarations and the
merged proved API do not advance any phase counter.

The [single unchanged full-suite recheck](bench-results/prerequisite-full-ci-recheck-77a844987.json)
of `77a844987` retains all 57 successful executable checks and a completed
382/360-second cap failure. Its remaining all-library oracle step was
cancelled after that failure. Available merged proofs and bounded #10575
consumer/import preparation remain independent of this timing concern.
[Certified parent isolation reuse](bench-results/number-field-isolation-reuse/README.md)
proves complete canonical-result equality and reduces measured hard arithmetic
by about 1.5 times, while preserving current representation and Phase-4 gaps.

[PR CI for #10695](bench-results/prerequisite-required-ci-d6cebc4de.json)
(head `d6cebc4de`, test merge `252f17576`) passes all 57 executables and every
conformance oracle at 284/360 seconds. The [source-scoped CI discussion](hex-real-algebraic-performance.md#concerns)
records the per-library soft warnings, the slower-runner limit, later main cap
changes and the retained local smoke and dependency failures. It establishes
no scientific Phase-4 admission. All four assigned counters remain 3.

## Current performance boundary

The [Sturm reconciliation](bench-results/sturm-policy-reconciliation.json)
checks direct dependencies and all 260 retained growing-bit observations.
The predeclared replay and growing-bit upper bounds have valid one-sided
observations on their measured sources; current policy does not impose a
mandatory dominant-phase profile. The growing-bit collection has only selected
source comparisons: full library-source provenance and import-cone/manifest
changes remain to be checked before it attests current Phase 4. The
[production integer-sign replacement](bench-results/sturm-sign-comparisons/README.md)
preserves `Int.sign` by a kernel-proved compiler equality and improves the
ratio of paired medians by 4.081× at degree 1024 on the bench-local
sign traversal of production-generated chains. Its unchanged quadratic
ladder and single permitted repeat remain inconclusive (+0.326483, +0.164190),
so sign-traversal characterization remains open; its older unchanged rerun
(+0.465232) also remains retained. Failed retargeting and
prepared-count two-sided declarations remain unresolved. Fixed hash anchors
have no performance claim, and theorem-only Mathlib layers have no dedicated
compiled performance deliverable.

Merged [#10766](https://github.com/kim-em/hex-dev/pull/10766) preserves complete
canonical-result equality while reusing parent isolation during exact addition
and multiplication. Its [retained paired evidence and degree plots](bench-results/canonical-parent-isolation-reuse/README.md)
show about 1.9–2.0× canonical-addition improvement and 1.14–1.27× real
square-root improvement at the recorded rungs. Real-root isolation remains the
main cost and the severe external gap remains a concern. Timing result hashes
are separate from the frozen-binary panic-rejecting verifier evidence.
[Required CI](https://github.com/kim-em/hex-dev/actions/runs/37317773840)
on reviewed head `dca7d35e70` passes the full library/conformance/oracle/trust
suite and benchmark verification at 412/600 filtered seconds. This is an
operational observation, not a performance budget. The four assigned libraries
still record 3; both cores have direct prerequisites at 7. Consumers #10377,
#10378 and #10575 can use the merged proved APIs without waiting for #10577.
