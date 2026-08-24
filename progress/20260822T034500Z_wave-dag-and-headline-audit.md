# Release wave: dependency DAG, bump queue, and headline-theorem audit

Reference artifact for the done_through-7 release wave (13 libraries:
Resultant, ResultantMathlib, NumberField x2, NumberFieldTower x2, RCF,
Berlekamp, BerlekampMathlib, BerlekampZassenhaus, BZMathlib,
RootsMathlib, PolyFpMathlib). Each later bump PR cites its edge here.

## Phase-dependency edges driving the order

Dep-coupled phases are 1, 3, 4 (PLAN/Conventions.md); 2, 5, 6, 7 are
local. The binding edges for this wave:

- Berlekamp P4 -> BZ P4 -> {NumberField, Tower} P4.
- PolyFpMathlib P4 -> BerlekampMathlib P4 -> BZMathlib P4 ->
  {NumberFieldMathlib, TowerMathlib} P4.
- RootsMathlib P3/P4 and ResultantMathlib P3/P4 -> NumberFieldMathlib
  P3/P4; those plus NumberFieldMathlib -> TowerMathlib P3/P4.
- BZ P1/P3 -> NumberField cluster P1/P3.
- RCF has no unmet dep edges (RealRootsMathlib is at 4).

## Bump queue (libraries.yml is a hot file; bumps land one at a time)

1. HexResultant 4->5, HexRCF 4->5 (this PR).
2. HexRootsMathlib 0->2, then 2->4.
3. HexResultantMathlib 3->4->5.
4. HexBerlekamp 3->4 (after comparator reclassification).
5. HexBerlekampZassenhaus 0->4.
6. HexPolyFpMathlib 0->4 (includes the headline-theorem work below).
7. HexBerlekampMathlib 3->4 (proof-track evidence).
8. HexBerlekampZassenhausMathlib 2->3->4.
9. NumberField cluster 0->1->2->3->4->5.
10. Phase 6 bumps per library as hygiene PRs land.
11. Phase 7 bumps, serialized, after chapters/headings/READMEs/
    tutorials; manual-split and released.yml changes last.

## Headline-theorem audit (PLAN/Conventions.md, binds at done_through >= 4)

House pattern: the designation lives in the companion's SPEC as a
"## Headline correctness theorem" section naming one theorem
(exemplars: HexLLLMathlib, HexBareissMathlib). Verdicts:

- HexResultant pair: theorem exists (`toPolynomial_resultant`,
  HexResultantMathlib/Sylvester.lean); designation added in this PR.
- HexRCF (integrated): theorem exists (`check_sound`,
  HexRCF/Soundness.lean); designation added in this PR.
- HexPolyFp pair: REAL GAP. HexPolyFp is at 7 but its companion has no
  end-to-end theorem (correspondence lemmas only), and the companion
  SPEC's "What belongs here" section currently forbids one. The
  PolyFpMathlib ladder PR must state and prove a Mathlib-side
  square-free-decomposition headline over `Polynomial (ZMod p)` and
  amend that SPEC section.
- HexBerlekamp pair: two co-equal key theorems; designate one
  (candidate `fpIsIrreducible_iff`,
  HexBerlekampMathlib/Irreducibility.lean:951) in the companion SPEC
  before the P4 bump.
- HexBerlekampZassenhaus pair: five-theorem family with #print axioms
  guards already; collapse into one designated headline (product +
  normalization + irreducibility + uniqueness over `ZPoly.factorize`)
  before the BZMathlib P4 bump.
- HexNumberField pair: per-operation headlines only; designate one
  end-to-end embedding-correctness statement before the P4 bump.
- HexNumberFieldTower pair: designate `NumberTower.factor?_sound`
  (Factor.lean:642) before the P4 bump.

Per-theorem `#print axioms` guards are BZ-SPEC practice, not a
Conventions requirement; the release-wide trust check is
scripts/release/check_trust_surface.py. Add guards opportunistically in
the Phase-6 passes.

## Accomplished

- Audited headline-theorem designations across the seven pairs (above).
- Recorded the wave DAG and bump queue.
- Bumped HexResultant and HexRCF to done_through 5 with their
  designation sections added.

## Current frontier

- check_phase7 integrated-Mathlib fix in review (#9375); Berlekamp
  comparator re-measurement queued on chungus2 behind machine idleness.

## Next step

- HexRootsMathlib Phase-2 review; Berlekamp comparator
  reclassification PR once refreshed measurements land.

## Blockers

- Timing refresh waits for the bench host to go quiet.
