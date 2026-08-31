# Phase-4 Ordered-Mode Audit

The pre-rollback inventory contains 58 local libraries recorded at
`done_through >= 4`. The review finds 22 libraries with open Phase-4 evidence
and 36 with no gap in the ordered-mode audit. All affected libraries are
rolled back to `done_through: 3` in
[`libraries.yml`](../libraries.yml) by PR
[#9816](https://github.com/kim-em/hex-dev/pull/9816).

The five libraries already rolled back directly by PR
[#9769](https://github.com/kim-em/hex-dev/pull/9769) are outside the current
inventory: HexBerlekampZassenhaus
([#9793](https://github.com/kim-em/hex-dev/issues/9793)), HexPolySmith
([#9742](https://github.com/kim-em/hex-dev/issues/9742)), HexGFqField
([#9740](https://github.com/kim-em/hex-dev/issues/9740)), HexHensel
([#9741](https://github.com/kim-em/hex-dev/issues/9741)), and HexRoots
([#9794](https://github.com/kim-em/hex-dev/issues/9794)). HexNumberField was
also reconciled and rolled back by #9769, but a later cluster bump restored it
to 7 while its report still states that Phase 4 is blocked. It is included
below because HexNumberFieldTower relies on it.

## Findings and rollbacks

| Library | Open evidence | Focused issue |
| --- | --- | --- |
| HexPoly | No multiplication comparator rung is eligible; the separate expected composition divergence is misfiled as a Concern and must move to the trend narrative. | [#9804](https://github.com/kim-em/hex-dev/issues/9804) |
| HexMvPoly | The representation experiment remains unresolved under `## Concerns`. | [#9805](https://github.com/kim-em/hex-dev/issues/9805) |
| HexMvGcd | Fixed shape/hash registrations are used as performance coverage without mode-3 budgets or ordered-mode exclusions. | [#9812](https://github.com/kim-em/hex-dev/issues/9812) |
| HexRowReduce | Advertised compiled operations have conformance evidence but no performance mode. | [#9811](https://github.com/kim-em/hex-dev/issues/9811) |
| HexBareiss | An unresolved informational-comparator finding remains under `## Concerns`. | [#9806](https://github.com/kim-em/hex-dev/issues/9806) |
| HexGF2 | The addition comparison is marshalling-dominated; the separate expected NTL divergence is misfiled as a Concern and must move to the trend narrative. | [#9807](https://github.com/kim-em/hex-dev/issues/9807) |
| HexLLL | The verified-Isabelle comparison has only one point per headline family. | [#9808](https://github.com/kim-em/hex-dev/issues/9808) |
| HexPolyFp | Frobenius and GCD remain inconclusive; no ordered-mode rationale makes either a pass. | [#9809](https://github.com/kim-em/hex-dev/issues/9809) |
| HexConway | Fixed Tier-1/Tier-2 checks lack mode-3 evidence, and the lookup verdict predates the current table. | [#9813](https://github.com/kim-em/hex-dev/issues/9813) |
| HexGFq | Fixed constructor/projection verdict surfaces lack mode-3 evidence and expected hashes. | [#9814](https://github.com/kim-em/hex-dev/issues/9814) |
| HexMvPolyMathlib | All five proof-track threshold comparisons remain unresolved under `## Concerns`. | [#9810](https://github.com/kim-em/hex-dev/issues/9810) |
| HexNumberField | The report remains blocked on incomplete API coverage and five registrations without passing modes. | [#9722](https://github.com/kim-em/hex-dev/issues/9722), [#9743](https://github.com/kim-em/hex-dev/issues/9743), [#9795](https://github.com/kim-em/hex-dev/issues/9795), [#9796](https://github.com/kim-em/hex-dev/issues/9796) |
| HexNumberFieldTower | The Trager envelope fails mode 2's dominant-phase test, and fixed component anchors are used as coverage without mode-3 evidence. | [#9815](https://github.com/kim-em/hex-dev/issues/9815) |
| HexRowReduceMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9817](https://github.com/kim-em/hex-dev/issues/9817) |
| HexDeterminantMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9818](https://github.com/kim-em/hex-dev/issues/9818) |
| HexBareissMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9819](https://github.com/kim-em/hex-dev/issues/9819) |
| HexModArithMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9820](https://github.com/kim-em/hex-dev/issues/9820) |
| HexGramSchmidtMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9821](https://github.com/kim-em/hex-dev/issues/9821) |
| HexPolyZMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9822](https://github.com/kim-em/hex-dev/issues/9822) |
| HexPolyZGcdMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9823](https://github.com/kim-em/hex-dev/issues/9823) |
| HexLLLMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9824](https://github.com/kim-em/hex-dev/issues/9824) |
| HexHenselMathlib | The report-less correspondence-only exemption lacks the required SPEC declaration. | [#9825](https://github.com/kim-em/hex-dev/issues/9825) |

There is no valid manual mode-2 pass in the affected set.
HexNumberFieldTower's candidate citation covers the BHKS factorization phase,
but the report attributes only 5.26% of the measured call to that phase.
HexPolyFp supplies neither a mode-2 citation nor the required inclusive
dominant-phase profile. HexNumberField's report already classifies its
remaining inconclusive registrations as mode 4.

## Inspected with no gap

HexBasic has no SPEC API surface and therefore no performance-evidence
registration to classify; the ordered-mode rule is vacuous for it. Its
pre-existing report-shape omissions are outside this reset.

The remaining headline reports contain passing two-sided registrations, no
unresolved Concern, or explicitly resolved historical evidence. Their passing
registrations remain unchanged:

- [HexBasic](hex-basic-performance.md) and
  [HexTruncatedSeries](hex-truncated-series-performance.md),
  [HexArith](hex-arith-performance.md),
  [HexPolyFast](hex-poly-fast-performance.md),
  [HexSparsePoly](hex-sparse-poly-performance.md),
  [HexMatrix](hex-matrix-performance.md),
  [HexDeterminant](hex-determinant-performance.md),
  [HexModArith](hex-mod-arith-performance.md),
  [HexModular](hex-modular-performance.md),
  [HexGramSchmidt](hex-gram-schmidt-performance.md),
  [HexPolyZ](hex-poly-z-performance.md),
  [HexPolyZGcd](hex-poly-z-gcd-performance.md),
  [HexHermite](hex-hermite-performance.md),
  [HexSmith](hex-smith-performance.md),
  [HexGFqRing](hex-gfq-ring-performance.md),
  [HexBerlekamp](hex-berlekamp-performance.md),
  [HexPolyMathlib](hex-poly-mathlib-performance.md),
  [HexMatrixMathlib](hex-matrix-mathlib-performance.md),
  [HexBerlekampMathlib](hex-berlekamp-mathlib-performance.md),
  [HexBerlekampZassenhausMathlib](hex-berlekamp-zassenhaus-mathlib-performance.md),
  [HexResultant](hex-resultant-performance.md),
  [HexRealRoots](hex-real-roots-performance.md),
  [HexRealRootsMathlib](hex-real-roots-mathlib-performance.md), and
  [HexRCF](hex-rcf-performance.md).

The remaining 12 libraries are correspondence-only Mathlib layers. They have
no performance-evidence registration or proof probe of their own, explicitly
declare `correspondence_only: true`, declare no `phase4` block, and carry the
required `correspondence-only-layer` SPEC declaration with computational
conformance and performance owners, so they are exempt from a local headline
report:

- [HexPolySmithMathlib](../HexPolySmithMathlib/SPEC/hex-poly-smith-mathlib.md),
  [HexSparsePolyMathlib](../HexSparsePolyMathlib/SPEC/hex-sparse-poly-mathlib.md),
  [HexHermiteMathlib](../HexHermiteMathlib/SPEC/hex-hermite-mathlib.md),
  [HexSmithMathlib](../HexSmithMathlib/SPEC/hex-smith-mathlib.md),
  [HexPolyFpMathlib](../HexPolyFpMathlib/SPEC/hex-poly-fp-mathlib.md),
  [HexGF2Mathlib](../HexGF2Mathlib/SPEC/hex-gf2-mathlib.md),
  [HexGFqMathlib](../HexGFqMathlib/SPEC/hex-gfq-mathlib.md),
  [HexTruncatedSeriesMathlib](../HexTruncatedSeriesMathlib/SPEC/hex-truncated-series-mathlib.md),
  [HexRootsMathlib](../HexRootsMathlib/SPEC/hex-roots-mathlib.md),
  [HexResultantMathlib](../HexResultantMathlib/SPEC/hex-resultant-mathlib.md),
  [HexNumberFieldMathlib](../HexNumberFieldMathlib/SPEC/hex-number-field-mathlib.md), and
  [HexNumberFieldTowerMathlib](../HexNumberFieldTowerMathlib/SPEC/hex-number-field-tower-mathlib.md).
