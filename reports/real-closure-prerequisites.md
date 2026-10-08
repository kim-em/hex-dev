# Sturm and real-algebraic prerequisite readiness

Scope: [#10577](https://github.com/kim-em/hex-dev/issues/10577), the implemented
HexSturm and HexRealAlgebraic pairs through Phase 4. This is development-library
readiness, not split-package publication or full distribution readiness.
The four-library audit below reuses merged computation, proofs, independent
scaffolding reviews and retained evidence. Final attestation requires green
required CI on the readiness PR.

| Library | Actual Phases 1–3 coverage | Phase-4 coverage and dependency requirement | Evidence |
| --- | --- | --- | --- |
| HexSturm | Shared ordered-domain kernel, exact natural root count, prepared domains/retargeting, literal certificates and replay, checked domains, transport, remainder-only value queries; compiled operation/property/edge and adversarial tests | Registered stages/frontends, rational/integer agreement, FLINT/Z3 orientation, retained ladders/profiles and explicit finding dispositions. Direct prerequisites HexPoly and HexRealRoots both record 7. | `HexSturm/Basic.lean`, `Transport.lean`, `Reduced.lean`, computational conformance; [performance report](hex-sturm-performance.md), [work derivation](sturm-readiness-work.md) |
| HexSturmMathlib | Semantic domain and prepared bindings, producer acceptance, noninjective coefficient interpretation, query iff and count semantics, representation congruence, rational/integer whole-Option agreement; ordinary-kernel tests and axiom guards | Theorem-only: no dedicated Phase-4 performance deliverable. Advance after HexSturm; other direct prerequisites HexPolyMathlib and HexRealRootsMathlib both record 7. | Ordinary `HexSturmMathlib` umbrella, `Soundness.lean`, `Domain.lean`, `Rational.lean`, `Reduced.lean`, `HexSturmMathlibTests` |
| HexRealAlgebraic | Real subtype, rational recognition/rounding fast path, arithmetic/order, approximation/Repr, square roots, fixed-field signs, integer/algebraic-coefficient roots, complex norms; compiled conformance and exact oracle | Actual scalar/root/comparison size plots, external comparators, source-scoped profiles and corrected redundant work. Seven audited family coverage decisions and practical limits. Direct prerequisite HexNumberField records 7. | `HexRealAlgebraic`, conformance, pinned FLINT fixtures/oracle; [performance report](hex-real-algebraic-performance.md) |
| HexRealAlgebraicMathlib | Closure/arithmetic/order, dictionary coherence, rational recognition, rounding/approximation/Repr roundtrip, fixed-field sign, root completeness/multiplicity/order, real closedness; ordinary-kernel tests and axiom guards | Theorem-only: no dedicated Phase-4 performance deliverable. Advance after HexRealAlgebraic; other direct prerequisites HexNumberFieldMathlib and HexRealRootsMathlib both record 7. | Ordinary companion umbrella, `Instances.lean`, `Roots.lean`, `RealClosed.lean`, `HexRealAlgebraicMathlibTests` |

Independent Phase-2 scaffold reviews remain in `status/`; the phase audit
preserves the implemented public semantics. No arithmetic, shared Tarski kernel
or root representation is duplicated, and no new axiom is introduced.

## Mathematical availability

`import HexSturmMathlib` exports `query_iff`, `query_sound`, `check_sound`,
`rootCount_eq` and the natural-count domain/bounds theorems. They do not require
roots to lie in the coefficient field. `rootCount_isSome` preserves precisely
the query domain; `query_nonneg`, `rootCount_query` and `rootCount_map` justify
`Int.toNat` for lawful query-one results. Supplied coefficient sign operations
must satisfy the correspondence hypotheses. The noninjective-storage tests
exercise these APIs without field/order instances on storage.

`AlgebraicNumber.realCompare_eq` and `realCompareExact_eq` in
`HexNumberFieldMathlib/Nearest.lean` establish the implemented comparison's
meaning; the subtype's `compare_eq` consumes them. `RealAlgebraicPoly.roots_spec`
is the root headline, with `contains_roots_iff`, `roots_all_iff`,
`roots_multiplicity` and `roots_sorted`: zero has the universal root set;
nonzero finite results are complete, ordered and have exact positive
multiplicities. `signField_spec` and `signField_eq` identify fixed-field signs.
Ordinary-kernel guards check these named theorems against only the three
standard logical axioms.

The shared root-sum foundation is in HexRealRootsMathlib; frontend semantics
are in HexSturmMathlib. HexQuerySemantics retains integration regression tests
and the remaining owners' adapters. Proof availability does not depend on an
unrelated timing result or formal phase metadata.

HexRealAlgebraic remains independent of HexSturm, HexSignDet and HexRealClosure.
Rational recognition constructs the core rational directly from a canonical
linear polynomial; `toRat?_formula` proves the former quotient result. The
rounding fast path and degree-one arithmetic are tested, including denominator
2^100.

The forward comparison-strategy extension at the end of
[Exact comparison strategies](../SPEC/Libraries/hex-real-algebraic.md#exact-comparison-strategies)
is outside this attestation. Its new point/lazy/fixed-field/tower comparison
algorithms and six comparator families belong to HexNumberField and
HexNumberFieldTower implementation work. This boundary does not waive the
implemented `realCompare`, `signField` or `RealAlgebraicPoly.roots` audit.

## Performance readiness and supported limits

The [Sturm report](hex-sturm-performance.md) reconciles obsolete pending
semantics, stage registrations, comparator agreement and required profile
attribution. The [work derivation](sturm-readiness-work.md) supplies the
operation/operand premises for fourteen predeclared quartic upper bounds;
five two-sided finite-range findings retain their verdicts with supported
object/limb explanations. The synthetic all-coefficient sign traversal is a
descriptive auxiliary reference: production signs endpoint values or leading
coefficients. All failures remain retained, and the compiler fix's isolated
sign improvement is not presented as a complete-query speedup.

[Complete-query curves](bench-results/sturm-external-degree/comparison.svg)
cover rational Chebyshev degrees 4–64 against Z3 RCF and FLINT. The recorded
degree-64 medians are approximately 5.6/14.9/35.3 ms, respectively. These are
matching exact-count problems with different internal algorithms. Very large
queries against a fixed quadratic still have quadratic bit work; the reduced
value API reduces quotient storage, not the full arithmetic cost.

The [real-algebraic report](hex-real-algebraic-performance.md) records coverage
judgments for actual downstream operations. [Root plots](bench-results/real-root-isolation-reuse/plots/roots-comparison.svg)
and [scalar plots](bench-results/canonical-parent-isolation-reuse/plots/scalar-comparison.svg)
show all retained observations and source-scoped external references.
Corrected degree-eight rational root enumeration costs about 94 ms, but
the retained pre-direct-certification square-root observation costs about
7.1 seconds at operand degree eight and produces degree 16. Its historical
isolation/refinement profile explains that recorded cost; later selected-root
certification changes the path and is not assigned those old timings. arbitrary
high-degree canonical arithmetic is not attested as interactive. Repeated
canonicalization is a poor consumer hot path. External parity is not an
acceptance target; these limits remain explicit rather than hidden by a phase
number. No extra profile or wrapper microbenchmark is needed without a
concrete unresolved performance question.

Every completed failed/inconclusive measurement is retained, including rejected
cache/fallback prototypes, cap failures and unchanged repeats. Historical
report copies preserve the original findings. The 38 lost raw profiles cannot
be reprocessed or counted as retained raw evidence; later persistent captures
supply source-scoped attribution. Host activity remains context, not a sample
exclusion rule. No blanket rerun or new timing collection accompanies this
final reconciliation.

## Verification

[Local verification](bench-results/prerequisite-phase4-verification.json)
records the four-library build, ordinary companion tests, computational
conformance, both benchmark verifiers, Mathlib-free import check, dependency
check, published trust-surface check and named-admission scan. The expanded
local real-algebraic fixture emitter and pinned FLINT oracle pass 92 exact
cases with zero unavailable-component skips. The companion/kernel guards
allow only `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, new
axiom or `native_decide` is admitted. Fixed expected hashes establish
correctness/bitrot, not scientific performance.

The [compiled import-cone comparison](bench-results/sturm-source-cone.json)
and [55 selected definitions](bench-results/sturm-selected-source.json)
record retained-source applicability, including toolchain/LeanBench pins and
intervening computational changes. These are source assessments, not claims
of current executable byte identity or reconstruction of unrecorded dirty edits.
Required CI must pass the final revision, including existing conformance,
oracles, architecture/trust/kernel checks and the unchanged operational bench
verification cap. Earlier green CI and historical cap failures remain linked
in the performance histories; they do not substitute for the final PR gate.

## Dependencies and consumers

Advance each core from 3 to 4 before its theorem-only companion, after checking
the direct dependencies above. No transitive library is silently promoted.
HexRank/HexRankMathlib readiness belongs to
[#10352](https://github.com/kim-em/hex-dev/issues/10352); the ordered-function
pair already records Phase 4 and is not re-audited. Transitive HexPolyFp concerns
remain with [#9809](https://github.com/kim-em/hex-dev/issues/9809).

[#10377](https://github.com/kim-em/hex-dev/issues/10377) owns sign determination
and BKR; [#10378](https://github.com/kim-em/hex-dev/issues/10378) owns tower/root
assembly, extension-depth/nested-evidence performance and samples;
[#10358](https://github.com/kim-em/hex-dev/issues/10358) owns the tactic/manual.
Their implementation files are not changed by this audit.
[#10575](https://github.com/kim-em/hex-dev/issues/10575) owns semantic adapter
integration/publication and the package-boundary audit. In particular, the
Sturm companion tests import monorepo `HexSturm.Fixtures`; split-package wiring
must provide it when published. This does not prevent mathematical consumers
from using the merged proofs now.

Runnable starting points are the checked examples in
[HexSturm's README](../HexSturm/README.md) and
[HexRealAlgebraic's README](../HexRealAlgebraic/README.md), and
`lake exe hexrealclosure_basic_conformance`. The latter's
[retained fixture and exact Z3 check](bench-results/sturm-current-disposition-verification.json)
exercise inverse/powers, positive enlargement, cubic roots and their order
relations. [Inherited infinitesimal integration evidence](bench-results/prerequisite-inherited-extension-evidence.json)
also checks the corrected de Moura–Passmore counts 3 and 2 and third-derivative
query zero. Those are consumer correctness fixtures, not tower performance
attestations. None of these consumers needs to wait for #10577 closure to use
the available APIs.
