# Foundation verified green; remaining work isolated to the 1558 body

> **CORRECTION (post-review): the "KEY INSIGHT" below — reuse the M2 descent over a
> "shared `ModPFactorSubset` family" — is UNSOUND and superseded.** A Codex review
> (`20260625T120647Z_handoff-critical-review.md`) confirmed against source: the M1
> endpoint is keyed on `choosePrimeData? core` while the M2 descent is keyed on
> `toMonicPrimeData? core = choosePrimeData? (toMonic core).monic` (a DIFFERENT
> prime selection), and the mod-`p` subset transport across the dilation was
> REFUTED (#7366, see `representsModP_correspondent` docstring Basic:20870). The
> corrected plan (direct M1/core descent via
> `modPSubsetPartitionHypotheses_of_choosePrimeData core`, change 1558's prime-data
> hypothesis to `choosePrimeData? core`, generic `size_eq_indicators_of_candidates`
> for `hsize`) lives in `RESUME_PROMPT.md`. Everything in the "Accomplished" and
> build-state sections below remains accurate and verified.

## Accomplished (all verified by build this session)

1. **Plan corrected** (Codex-corroborated): the dilate `liftedTrueSupports`
   family re-hits #8319; `dilate ≠ scale` from defs. See
   `20260625T070000Z_…` / `20260625T083000Z_…`.
2. **Extraction lemma landed (exec green):**
   `bhksIndicatorCandidateCore?_eq_some_elim` (HexBerlekampZassenhaus/Basic.lean).
3. **monic_dvd design bug fixed + VERIFIED (CLDColumnBound green, 3771 jobs):**
   dropped the vestigial, undischargeable `monic_dvd` field from
   `RecoveredAtLiftM1` / `recoveredAtLiftM1_of_recovery` /
   `cutProjectionHypotheses_of_recoveryData` (never consumed on the M1 cut path).
4. **Refactor threaded + dead code deleted + VERIFIED (PartitionRefinement):**
   removed the now-stale `hmonic_dvd` args/hypotheses from
   `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveryData` (962/1002)
   and `…_of_coreLiftDataRecoveryData` (1020 endpoint, 1084/1163); deleted the
   two dead schedule theorems
   (`…_eq_expected_of_forwardInputs_on_schedule/at_cap_of_no_prior_recovery`,
   the source of error 530, zero users, off the soundness path).

**Build state now: `PartitionRefinement` has exactly 3 errors, ALL inside
`factorFastCore_irreducible_of_liftedTrueSupport` (now line 1493; errors at
1606/1678/1681) — the `hrows` coreLiftData-vs-toMonicLiftData mismatches in its
still-M2 body.** Error 530 gone; refactor introduced no new breakage. Only other
warning is the pre-existing `Basic.lean:233 isIrreducible_iff` sorry.

Uncommitted WIP touches: exec `Basic.lean`, Mathlib `Basic.lean`,
`CLDColumnBound.lean` (all verified green), and `PartitionRefinement.lean`
(refactor threading + 530 deletion compile; 1558 body still M2 → 3 errors).

## The ONE remaining task: rewrite the 1558 body to the M1 path

`factorFastCore_irreducible_of_liftedTrueSupport` (1493) must stop feeding the M2
bridge `…_of_recoveredLift` (via `recoveredLiftOfLiftedTrueSupport`, 1274) and
instead feed the now-clean M1 endpoint
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_coreLiftDataRecoveryData`
(962). The 1020 endpoint NO LONGER requires `hmonic_dvd`; its per-support inputs
are: `factor`, `cof`, `modPSubset`, `cofactor`, `cofactorLc`(>0), `hlc`,
`hfactor_size`, `hgcd_factor`, `hfactor_product` (monicTarget congruence),
`hrepP` (RepresentsIntegerFactorModP), `hfactor_prim`, `coeffBound`/`hvalid`/
`hprecision_factor` (Mignotte), `hsupp`, `hfac`, `hfactor`; plus scalars
(hp/hk/hsep/hthr/hselected/hcore_pos/hcore_size/hprecision/hgcd_core), the M1
`trueSupports`, `hsize`, `hpartition`.

KEY INSIGHT (verify before relying on it): the M1 supports are
`liftedSubsetOfModPSubset primeData (coreLiftData …) S₀` for the SAME shared
`ModPFactorSubset primeData` family the M2 `liftedTrueSupports core
(toMonicLiftData …)` uses (both Hensel-lift the same `primeData.factorsModP`).
So BOTH the count (via the generic `supportPartitionByMinColumn_length_eq_ncard_of_partition`
PartitionRefinement:208 + injectivity of `liftedSubsetOfModPSubset`) AND the
per-support DATA (factor / modPSubset / `RepresentsIntegerFactorModP` /
`monicTarget` congruence — coordinate-agnostic primeData facts) should transport
from the existing M2 descent `monicCorrespondentDescent_of_representsAtLift`
(IntReductionMod:3134), avoiding a fresh M1 descent.

OPEN CHECK before building: the M2 descent yields `RepresentsIntegerFactorModP
primeData gf S₀` with `gf` the M2 monic correspondent; the 1020 endpoint wants it
for `monicTarget factor primeData.p prec`. Confirm `gf` and `monicTarget factor`
have the same mod-p representation (both monic, both ≡ factor's mod-p factor
product) — read `RepresentsIntegerFactorModP` (Basic:1760) and find/prove the
`gf ↔ monicTarget factor` mod-p bridge. If that bridge is missing, it is the next
real sub-lemma (small, mod-p only — NOT a #8319-style wall).

Suggested order: (a) define M1 `trueSupports` + prove cover/disjoint/nonempty by
transport from the modP family; (b) the per-support certificate (reuse M2 descent
+ the mod-p bridge + `coreLiftData_subset_congr_monicTarget` Basic:10547 +
`honestCongr_of_product_congr_monicTarget` Basic:20403 + `hfac` from
`coreLiftData_liftedFactor_hensel_semantics` LiftBridge:692); (c) scalars + hsize
(`factorFastCoreWithBound_some_size_eq_indicators`) + hpartition; (d) build green;
(e) wire `factor_irreducible_of_nonUnit` FactorSoundness:18.

## Blockers

None mathematical; both latent design bugs resolved and verified. Remaining is the
large-but-mechanical 1558 assembly over ~11-min PartitionRefinement builds. The
`hsize` hypothesis of the current 1558 (the monic-vs-core indicator-size bridge)
likely disappears on the M1 path (coreFactors.size = coreLiftData-basis indicators
is exactly what the executable gives via `…_some_size_eq_indicators`), simplifying
the signature — re-derive rather than thread the old monic `hsize`.
