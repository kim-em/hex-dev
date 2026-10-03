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
the theorem-only companions need their cores at Phase 4 and the Sturm headline's
bridge-target availability reconciled before recording it.

| Library | Implemented/proved coverage | Phase requirements still to discharge | Evidence |
| --- | --- | --- | --- |
| HexSturm | Shared ordered-domain kernel; guarded queries and exact-domain natural counts; prepared domains, retargeting, counts, cached replay and literal certificate transport | Phase 4: comparator/registration reconciliation, admissible characterization and retained concerns | `HexSturm/Basic.lean`, `Transport.lean`, `conformance/HexSturm/Conformance.lean`, [performance report](hex-sturm-performance.md) |
| HexSturmMathlib | Domain equivalence, prepared bindings, producer acceptance, representation congruence and rational/integer whole-Option agreement; exact query iff, count equality and bounds in development adapters | Phase 4: core eligibility and headline bridge-target reconciliation; no dedicated performance deliverable for this theorem-only layer | `Domain`, `Compare`, `Rational`, `DenominatorClearing`, `IntCast`; `adapters/HexSturmMathlib/Soundness.lean`; ordinary-kernel `HexSturmMathlibTests` |
| HexRealAlgebraic | Real subtype, rational recognition and toRat?-first rounding, canonical arithmetic/order, rounding, square roots, fixed-field coordinate signs, integer and algebraic-coefficient real roots, complex norms | Phase 4: canonical fixed operations need admissible models/budgets; root/leaf, separation and rounding sweeps remain | `conformance/HexRealAlgebraic`, pinned FLINT/qqbar oracle and fixtures; `bench/HexRealAlgebraic/Bench.lean` |
| HexRealAlgebraicMathlib | Arithmetic/order and closure, law/dictionary coherence, rational recognition, rounding, approximation, Repr round trip, fixed-field sign correspondence, combined roots contract and real closedness | Phase 4: core eligibility; no dedicated performance deliverable for this theorem-only layer | `HexRealAlgebraicMathlib/Instances.lean`, `Roots.lean`, `RealClosed.lean`, `HexRealAlgebraicMathlib/Tests.lean` |

## Semantic availability

`HexQuerySemantics` builds the shared root-sum foundation and the Sturm
frontend adapters. `HexSturmMathlib.query_sound` and `check_sound` do not require
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
and a denominator of 2^100.

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
The real root headline builds in the companion target. The Sturm
semantic results currently build through `HexQuerySemantics` under `adapters/`;
Phase-4 evidence must reconcile their bridge-target availability with that
policy. Split-package integration remains with #10575 and is not asserted by
these monorepo results. In particular, the companion replay tests import the
conformance fixture module `HexSturm.Fixtures`; split-package test wiring must
provide it when those libraries are published. Available mathematical proofs do not depend on that
publication work.

## Dependencies and downstream owners

HexSturm's direct prerequisites are HexPoly (4) and HexRealRoots (7).
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
The transitive HexPolyFp performance concerns belong to
[#9809](https://github.com/kim-em/hex-dev/issues/9809); no unrelated counter is
promoted by this assignment.

## Verification

Local Lake builds pass for all four libraries and `HexQuerySemantics`.
The expanded real-algebraic conformance module and `HexRealAlgebraicMathlibTests`
compile. The axiom guards admit exactly `propext`, `Classical.choice`, and
`Quot.sound`; no new axiom, admission or native_decide is introduced.
The Mathlib-free benchmark target compiles and all shipped-API verification cases pass.
[Retained fixed-case baseline observations](bench-results/real-algebraic-readiness-baseline/results.json)
are not performance attestation: their 30-second operational caps are not
justified regression budgets. Independent review tokens are present; compiled conformance and the pinned
83-case core and 92-case local exact oracles pass with no skipped operations.
[The earlier rebase verification record](bench-results/prerequisite-rebase-verification.json)
retains checks and failed runs on its recorded bases, including inherited
field-sign conformance and ordinary-kernel axiom guards.
[The conversion/API rebase verification](bench-results/prerequisite-conversion-rebase-verification.json)
identifies checks on base `c74bc64a0`, including both companion test targets.
The square-root simplification has 83 fresh exact-oracle cases with zero skips;
fresh fixtures match the committed file byte for byte. Required CI on
[PR #10580](https://github.com/kim-em/hex-dev/pull/10580) checks the phase
recording and final revision before merge.
[The raw-artifact availability check](bench-results/prerequisite-profile-availability.json)
finds 38 prerequisite-readiness capture directories unavailable at their recorded
local paths. Committed manifests, summaries, diagnostics and completed timing
samples remain retained. [Three required representative captures](bench-results/prerequisite-representative-profiles-62399ddd0/README.md)
now supply replay, prepared-query and canonical-addition attribution with raw
perf/samply data, kernel sidecars and 126 matching artifact checksums in
persistent storage. They pass calibration and sensitivity checks; they do not
replace completed measurements or admit unresolved complexity models.
The [real-algebraic performance report](hex-real-algebraic-performance.md) and
the Sturm report distinguish valid family passes from failed hypotheses,
controls and fixed observations without budgets. Phase 4 remains incomplete.
