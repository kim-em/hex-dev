# Phase 4/5/6 checkpoint 60

Scope: checkpoint for the 42 PRs merged after summarize issue #7653 (closed
2026-06-17T05:29:27Z) through PR #7791 (`factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut`).
One thread dominates this window: the executable→Mathlib **transport** build-out
in `HexBerlekampMathlib/Basic.lean`. Forward and reverse Rabin transport now
compose into a full irreducibility iff, the `fpPolyEquiv` ring equivalence and
FpPoly degree/monicity/irreducibility transports landed, the Hensel
Mathlib-bridge dischargers were completed, and the gcd transport was put on a
sound normalize/associated footing. This retired the bulk of the
`HexBerlekampMathlib` proof debt (19 → 1 `sorry`) and all of the
`HexHenselMathlib` debt (6 → 0). A secondary thread continued the fast-path BHKS
van Hoeij CLD recombination chain up to the forward `_of_cut` raw-irreducibility
wrapper. The directive #2564 (HO-1) headline `sorry`s were **not** retired; a new
Berlekamp completeness chain (#7788 → #7789 → #6672) opened to feed them.

## Landed work

42 PRs merged after checkpoint 59 (range #7684–#7791). Grouped by topic.

### Executable→Mathlib transport in HexBerlekampMathlib (dominant theme)

The proof-facing bridge from the executable `FpPoly`/Rabin/Hensel/gcd surface to
the corresponding `Mathlib` `Polynomial (ZMod p)` facts. This window cleared
`HexBerlekampMathlib/Basic.lean` from 19 `sorry`s to 1 and `HexHenselMathlib`
from 6 to 0:

- **Rabin transport.** #7757 prove the Nat divisor-quotient prime lemma; #7733
  prove the Rabin finite-field bridge lemmas; #7776 prove the forward leg
  (`rabinTest_true_to_mathlib_checks`); #7780 prove the reverse leg
  (`rabinTest_true_of_mathlib_checks`). The two legs now compose into the Rabin
  irreducibility iff `rabinTest f = true ↔ Irreducible (toMathlibPolynomial f)`.
- **FpPoly transport.** #7740 prove the `fpPolyEquiv` ring-equivalence round-trip
  and ring-hom structure (`Hex.FpPoly p ≃+* Polynomial (ZMod p)`); #7761
  transport FpPoly monicity and degree; #7784 transport FpPoly irreducibility
  (`irreducible_toMathlibPolynomial_of_fpPolyIrreducible`).
- **Hensel bridge dischargers.** #7684 discharge `hensel_extends` mod-p
  reduction; #7688 discharge `quadraticHenselStep_monic`; #7699 discharge
  `quadraticHenselStep` uniqueness; #7719 expose linear Hensel discharge lemmas
  (nonconstant `g`); #7745 expose the Mathlib Hensel split uniqueness bridge
  lemmas; #7747 repair the linear `henselLift` bridge prerequisites; #7727
  discharge the coefficient-transport bridges (coeff + derivative).
- **gcd transport.** #7768 add sound normalize/associated gcd transport
  primitives (replacing the unsound exact `toMathlibPolynomial_gcd` placeholder);
  #7778 migrate the Berlekamp gcd transport consumers onto them.

### Fast-path BHKS CLD recombination chain

The van Hoeij CLD route feeding the fast-BHKS raw-irreducibility disjunct:

- #7686 add the product-side CLD aggregation lemma; #7695 prove product-side CLD
  aggregation for `TrueFactorLift`; #7708 prove the BHKS Lemma 5.7 carry core for
  the tight `psiCut` column bound; #7718 finish the tight `psiCut` aggregation
  bound; #7734 expose the per-support tight CLD norm-bound family for the cut
  projection.
- #7707 bridge `LiftData` subsets to BHKS true factors; #7724 derive BHKS
  semantics for monic lift supports; #7723 compose the true-factor cut stack into
  fast BHKS irreducibility.
- #7728 bridge the linear multifactor invariant to the quadratic invariant under
  raw monic heads; #7753 prove the recursive multifactor linear-quadratic
  agreement.
- #7738 bridge fast-core forward inputs to recorded entries; #7746 expose the
  fast-BHKS raw disjunct from the first-success state; #7791 add the forward
  `factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut` raw-irreducibility
  wrapper (no `BHKS.ForwardRecoveryInputs` parameter, routed through `_of_cut`).

### Slow/modular conformance guards

- #7775 add the slow-trial subset-product bucket guard; #7781 add the BZ
  slow-backstop subset-bucket conformance guard.

### Reviews and docs

- Reviews: #7687 (TrueFactorLift bridge + CLD-vector producer), #7691 (tight-CLD
  cut-projection consumption surface), #7698 (product-side CLD aggregation), #7713
  (`quadraticHenselStep` uniqueness mod p^(2k)), #7731 (`tightColumnBound`
  aggregation), #7748 (multifactor lift agreement), #7752 (BZ good-prime unit-gcd
  fallback boundary), #7754 (BZ subset-product recombination coverage), #7759 (BZ
  scalar and multiplicity coverage).
- Docs: #7693 record the Hensel Mathlib-bridge discharger soundness audit; #7769
  correct a stale CI claim in the `hex-lean-mathlib-boundary` skill.

## Phase state

`scripts/status.py` reports the executable dispatch front unchanged from
checkpoint 59. Phase-6 ready: HexArith, HexPoly, HexMatrix, HexModArith,
HexGramSchmidt, HexGF2, HexPolyZ, HexLLL, HexPolyFp, HexGFqField, HexHensel,
HexConway, HexGFq, HexPolyMathlib. `HexBerlekamp` is at Phase 4.
`HexBerlekampZassenhaus` remains at Phase 1 (library scaffolding), consistent
with directive #2564's `done_through: 2 → 0` rollback still standing.

Mathlib-side queues, unchanged from checkpoint 59:

- Phase 5 ready: HexMatrixMathlib, HexModArithMathlib.
- Phase 4 ready: HexGramSchmidtMathlib, HexPolyZMathlib, HexHenselMathlib,
  HexGF2Mathlib.
- Blocked: HexLLLMathlib (waits on HexGramSchmidtMathlib ≥ 4),
  HexBerlekampMathlib (waits on HexBerlekamp ≥ 4), HexGFqMathlib (waits on
  HexGF2Mathlib ≥ 4), HexBerlekampZassenhausMathlib (Phase 3, waits on
  `HexBerlekampZassenhaus.done_through ≥ 3`).

HexGFqRing is fully done. HexRoots/HexResultant/HexNumberField and their Mathlib
counterparts remain SPEC-ready but implementation-deferred.

## Quality metrics

Repository-wide Lean grep (`rg`, excluding `.lake/`):

- `sorry`: 44 raw `\bsorry\b` hits (down from 68 at checkpoints 57–59), of which
  **40 are genuine tactic `sorry`s** and 4 are prose (forbidden-token checklist
  text in `HexBerlekampZassenhausMathlib/IntReductionMod.lean:1275`, a prose line
  in `HexBerlekampZassenhausMathlib/Basic.lean:231`, a `GF2q.lean` docstring hit,
  and the `bareiss_eq_det` reference comment in
  `HexMatrixMathlib/Determinant.lean:24`). The 24-hit drop is real progress, not
  a counting change: the transport thread cleared `HexBerlekampMathlib`
  (19 → 1) and `HexHenselMathlib` (6 → 0).

  The 40 genuine tactic `sorry`s split as:
  - **37 in the GF2/GFq Mathlib scaffolding layers**, not on the directive #2564
    critical path: HexGF2Mathlib 23 (Field.lean 12, Basic.lean 11), HexGFqMathlib
    14 (GF2q.lean 7, Basic.lean 7).
  - **3 capstone-gated bridges** on the directive #2564 chain:
    `irreducible_of_mem_berlekampFactor` (`HexBerlekampMathlib/Basic.lean:960`,
    needs #7789), `Hex.ZPoly.isIrreducible_iff`
    (`HexBerlekampZassenhausMathlib/Basic.lean:235`, #4818), and
    `factor_irreducible_of_nonUnit`
    (`HexBerlekampZassenhausMathlib/FactorSoundness.lean:20`, #6672).

  No `sorry` exists in any Mathlib-free executable library. The Mathlib bridge
  layers that do carry `sorry`s still compile (a `sorry` is a warning, not an
  error), so `ci.yml`'s build of `HexBerlekampZassenhausMathlib` /
  `HexBerlekampMathlib` stays green while these obligations remain open.

- `axiom`: 0 real declarations. The 11 `\baxiom\b` grep hits are all comment /
  docstring text — `Lean.Grind.Semiring` / `Field` axiom-*field* references in
  `HexGFqRing/Operations.lean` and `HexPolyFp/Quotient.lean`, plus one
  forbidden-token checklist line. No line begins with `axiom`.

- `native_decide`: 0 real tactic uses. The 2 grep hits are both comment text (a
  checklist line in `HexBerlekampZassenhausMathlib/IntReductionMod.lean:1275` and
  a line in `HexArith/Nat/Prime.lean:344` stating the code does *not* depend on
  `native_decide`).

## Blocking structure for directive #2564

The headline gap is unchanged: the directive #2564 capstone is the two
`HexBerlekampZassenhausMathlib` `sorry`s
(`factor_irreducible_of_nonUnit`, `Hex.ZPoly.isIrreducible_iff`), both still
open. This window built substrate and transport API around them without retiring
either. Two fronts feed them:

1. **Berlekamp completeness chain (new this window).** The transport build-out
   exposed a clean route to the executable Berlekamp irreducibility:
   #7788 → PR #7794 (`irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd`,
   divisor-generalized completeness, in CI) → #7789 (executable per-member
   `berlekampFactor_factors_irreducible`, `blocked` on #7788) → discharge of the
   Mathlib-side `irreducible_of_mem_berlekampFactor` `sorry`
   (`HexBerlekampMathlib/Basic.lean:960`). #7789 is the live critical-path issue
   feeding the HexBerlekampMathlib bridge.

2. **Fast-path BHKS recovery.** The forward `_of_cut` raw-irreducibility wrapper
   `factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut` (#7791,
   `PartitionRefinement.lean`) is now in place with no `ForwardRecoveryInputs`
   parameter. Its **coverage producer remains unproduced**: #7793 (BHKS
   first-success coverage producer) is unclaimed and, per the #7786 stop-and-
   comment carried into its body, is blocked on a missing substrate — every
   `∀ S, BHKS.TrueFactorLift L S` occurrence in the layer is a hypothesis, never
   a conclusion, and the only constructors (`trueFactorLiftOfSubset` /
   `trueFactorLiftSemanticsOfToMonicSubset`, `LiftBridge.lean:78,104`) demand an
   exact `liftedFactorProduct d T = factor` witness per support that nothing in
   the tree currently supplies. An unconditional form additionally needs the
   scheduled-loop determinism `hcore` (a BHKS precision-soundness theorem not in
   the tree).

The HO-1 capstone #6672 (`factor_irreducible_of_nonUnit` assembly) consumes
whichever front lands first; its body notes it remains **not claimable** until a
fast unconditional raw-irreducibility substrate
(`factorFastRaw_irreducible_of_some`) is planned, sibling to the two already-
available slow disjuncts (`factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none`
and `slowModularRaw_irreducible_of_fast_none`, `IntReductionMod.lean:6422,6225`).

## Current frontier

Open PRs at checkpoint time:

- #7794 feat: prove divisor-generalized Berlekamp completeness
  (`irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd`) — closes #7788.
- #2656 spec: add hex-real-roots and hex-sturm (status: planned).

Unclaimed issues (excluding this summarize issue): #6672 (HO-1 capstone, not yet
claimable — needs the fast substrate planned), #7793 (BHKS first-success coverage
producer, blocked on the missing per-support exact-lift substrate). Directive
#2564 remains the open umbrella.

## Recommended next actions

1. Land PR #7794, then dispatch #7789 (executable per-member Berlekamp
   irreducibility) — the cleanest live route to retiring the
   `irreducible_of_mem_berlekampFactor` bridge `sorry` and feeding the HO-1
   capstone.
2. Plan the missing BHKS substrate that #7793 and #6672 both need: a producer
   concluding the per-support `∀ S, BHKS.TrueFactorLift L S` family (plus
   semantics) from the first-success recovery's exact
   `liftedFactorProduct d T = factor` witness. Until that exists, #7793 should be
   stop-and-commented, not bashed through with added hypotheses.
3. Do **not** construct or take `BHKS.ForwardRecoveryInputs` (its
   `lattice_eq_indicators` field is the dead reverse separation, blocked on
   #6779/#2564) and do not weaken the fast disjunct to an existential
   `bhksRecover?` extraction — neither feeds the raw-irreducibility endpoint.
4. Continue the executable→Mathlib transport thread opportunistically; it is the
   highest-yield recent vein (24 `sorry`s retired this window) and the
   GF2/GFq scaffolding layers (37 remaining genuine `sorry`s) are the next
   natural target once their dependency phases unblock.
