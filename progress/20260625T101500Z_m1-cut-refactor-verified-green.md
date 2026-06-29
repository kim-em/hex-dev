# M1 cut path: monic_dvd design bug fixed and VERIFIED GREEN

## Accomplished

Two verified green deliverables this session, plus the plan correction.

**1. Extraction lemma (executable layer, green).**
`bhksIndicatorCandidateCore?_eq_some_elim` (HexBerlekampZassenhaus/Basic.lean,
after `bhksIndicatorCandidateCore?_dvd`): inverse soundness — from a successful
indicator candidate, extracts the selected subset, the M1 scale-recovery formula,
and the cofactor quotient. `lake build HexBerlekampZassenhaus.Basic` green.

**2. monic_dvd design bug fixed + VERIFIED.**
The M1 endpoint chain required `monic_dvd : monicFactor ∣ monicTarget core` (exact
ℤ[x]), which is undischargeable for proper factors (`monicTarget core` is a centred
mod-`p^k` reduction; its ℤ[x] factorisation does not track `core`'s). It mirrored
the M2 field `∣ (toMonic core).monic` (which IS dischargeable) against the wrong
target. Traced every consumer: `RecoveredAtLiftM1.monic_dvd` is **never projected**
— the M1 cut path (`cutProjectionHypotheses_of_recoveredM1` →
`congr_logDeriv_bridge_of_recoveredM1` → `exists_scale_congr_factor_of_recoveredM1`
→ `candidate_eq`) uses only `congr` + `recovered_eq`; all `.monic_dvd` consumers are
the M2 `RecoveredAtLift`. Removed the field:
- `RecoveredAtLiftM1` structure (Basic:3370): dropped `monic_dvd`.
- `recoveredAtLiftM1_of_recovery` (Basic:6050): dropped `hmonic_dvd` param + field.
- `cutProjectionHypotheses_of_recoveryData` (CLDColumnBound:2774): dropped the
  `hmonic_dvd` hypothesis + its use.
- docstrings updated (3).
**`lake build HexBerlekampZassenhausMathlib.CLDColumnBound` GREEN** (3771 jobs;
Basic 31s, Recovery 689s, CLD 12s). Only warning is the pre-existing
`Basic.lean:233 isIrreducible_iff` sorry (C1, not ours). No new sorry/axiom.

This was the genuine remaining obstruction. The M1 cut endpoint
`cutProjectionHypotheses_of_recoveryData` now takes ONLY dischargeable per-support
inputs: `factor`, `cof`, `subset`, `monicFactor`, `cofactorLc` (>0), `hcongr`
(reduceModPow id), `hhonest` (proportional congruence), `hfactor_prim`,
`coeffBound`/`hvalid`/`hprecision` (Mignotte), `hsupp`, `hfac`, `hfactor`.

## Build-cost note

Editing Mathlib `Basic.lean` forces a Recovery rebuild (~689s) on the next
downstream build. Batch Basic edits. `PartitionRefinement` (~11 min) does NOT
rebuild Basic/Recovery when they are cached.

## Next step (certificate + wiring — the remaining work, obstructions now cleared)

1. **Fix the stale callers of the refactored signatures** (currently the only
   thing keeping PartitionRefinement red beyond the original 4 errors):
   - PartitionRefinement 1020 endpoint `..._of_coreLiftDataRecoveryData` passes
     `hmonic_dvd` to `cutProjectionHypotheses_of_recoveryData` (~line 997) and
     carries an `hmonic_dvd` hypothesis (~1088): both now removed-arg / unused —
     delete them.
2. **Per-support certificate** (in PartitionRefinement, feeding either the 863
   endpoint or `cutProjectionHypotheses_of_recoveryData` directly): for each true
   support, set `monicFactor := monicTarget factor`, get
   - `hcongr` from `coreLiftData_subset_congr_monicTarget` (Basic:10547) +
     `reduceModPow_eq_of_congr`,
   - `hhonest` from `honestCongr_of_product_congr_monicTarget` (Basic:20403),
   - `factor`/`cof`/`hfactor`/`cofactorLc`/`hlc`/recovery formula from the
     executable extraction lemma + the Recovery indicator↔subset bridges
     (`bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports`
     Recovery:1573, `polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct`
     Basic:5635),
   - `hfac` from `coreLiftData_liftedFactor_hensel_semantics` (LiftBridge:692),
   - Mignotte from `two_mul_defaultFactorCoeffBound_core_lt_pow_of_cldCoeffFloor_le`.
3. **M1 trueSupports + count transport** (probe confirmed viable): define
   trueSupports as the image of the shared modP true-support family under
   `liftedSubsetOfModPSubset primeData (coreLiftData …)`; transport
   cover/disjoint/nonempty (injectivity + subset/disjoint-iff lemmas Basic:2301+)
   and apply the GENERIC
   `supportPartitionByMinColumn_length_eq_ncard_of_partition`
   (PartitionRefinement:208); ncard = modP count = card from the M2 chain
   (`…_of_toMonicPrimeData` PartitionRefinement:260).
4. Rewrite `factorFastCore_irreducible_of_liftedTrueSupport` (1558) over
   coreLiftData feeding the above; fix the independent 530 schedule theorem
   (re-point to coreLiftData or delete if dead); `lake build PartitionRefinement`
   green; wire `factor_irreducible_of_nonUnit` (FactorSoundness:18).

## Blockers

None mathematical. The two latent design problems (dilate/scale family mismatch;
vestigial undischargeable monic_dvd) are both resolved. Remaining work is
mechanical assembly over ~11-min PartitionRefinement builds. Tree state: exec
`Basic.lean` + Mathlib `Basic.lean` + `CLDColumnBound.lean` carry the verified
changes (uncommitted WIP); `PartitionRefinement.lean` still at the 4-error state
plus the now-stale 1020 `hmonic_dvd` caller (step 1 above).
