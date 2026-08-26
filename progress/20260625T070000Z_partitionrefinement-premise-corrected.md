# PartitionRefinement migration: refined plan premise is WRONG — corrected target

## Accomplished

Captured the baseline build (`lake build HexBerlekampZassenhausMathlib.PartitionRefinement`):
4 real errors confirmed — `530`, `1671`, `1743`, `1746` (log:
`scratchpad/pr_build_baseline.log`). All four are the same root cause: the
executable `factorFastCoreWithBound_some_indicatorCandidates`
(HexBerlekampZassenhaus/Basic.lean:13033) now yields `hrows` / candidate data
over `coreLiftData core k' primeData`, while the body of
`factorFastCore_irreducible_of_liftedTrueSupport` (PartitionRefinement:1558) is
still entirely `toMonicLiftData`/dilate. (Error 530 is a SEPARATE theorem,
`factorFastCoreWithBound_eq_expected_of_forwardInputs_on_schedule_of_no_prior_recovery`
(516), also broken by the executable swap — its `hno` over `toMonicLiftData`
no longer matches the now-coreLiftData `bhksRecover?` schedule.)

**Ran a full premise check (corroborated by Codex second opinion). The
"REFINED PLAN" in `20260625T000000Z_...` is wrong on every load-bearing point.**

## The premise failure (concrete evidence)

The refined plan said: feed the M1 endpoint
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_coreLiftDataRecoveryData`
(1020) its decomposed per-support witnesses (factor / cof / modPSubset /
cofactorLc / hlc / hgcd_factor / hfactor_product / hrepP / hmonic_dvd / hsupp /
…), sourcing them from the coreLiftData SCALE recovery
`candidatesOfScaledCenteredLift` (Recovery:2742) →
`ForwardRecoveryInputsCore.ofMignottePrecisionCandidateProducts` (Recovery:2794).

1. **Wrong source.** `candidatesOfScaledCenteredLift` /
   `ForwardRecoveryInputsCore` only build the *aggregate indicator-candidate
   fold* `bhksIndicatorCandidatesCore? f d expectedIndicators = some
   expectedFactors` (Recovery:2522). They do NOT produce the per-support descent
   bundle (factor S, modPSubset S, hrepP S, hfactor_product S, hmonic_dvd S) the
   1020 endpoint consumes. Different recovery route.

2. **`liftedTrueSupports` descent re-hits #8319.** The natural trueSupports for
   1020 is `liftedTrueSupports core (coreLiftData …)` (Basic:3959), but its
   membership witness is `RepresentsIntegerFactorAtLift core d f S =
   Nonempty (RecoveredAtLift …)` (Basic:2400), and `RecoveredAtLift`
   (Basic:2378) / its eliminator (Basic:2418) carry the **dilate**-coordinate
   equality `primitivePart (dilate (leadingCoeff core) monicFactor) = factor`.
   That dilate coordinate IS the #8319 wall — descending the lifted true
   supports re-enters exactly the coordinate the executable swap moved off.

3. **To-monic descent reuse is the wall again.**
   `monicCorrespondentDescent_of_representsAtLift` (IntReductionMod:3134) yields
   `gf` monic with `gf ∣ (toMonic core).monic` (M2) plus
   `RepresentsIntegerFactorModP primeData gf S₀` and the dilation back to `f`.
   It does NOT directly give `monicTarget (factor) p k ∣ monicTarget core p k`
   (M1 / scale `hmonic_dvd`) nor `RepresentsIntegerFactorModP primeData
   (monicTarget factor …) S₀`. Bridging M2-`gf`/dilate ↔ M1-`monicTarget`/scale
   is a substantial new proof and is #8319 in another guise.

4. **Prime-data mismatch.** 1020 is stated over `choosePrimeData? core = some
   primeData`; the old 1558 body is over `toMonicPrimeData? core = some
   primeData`. Another sign the surface must be core/M1, not patched M2 reuse.

So `factorFastCore_irreducible_of_liftedTrueSupport` is NOT a mechanical
lift-swap. The real remaining work is the SOUNDNESS CERTIFICATE that
FactorSoundness:356 already flags as the single open obligation:

> the fast BHKS core-success arm … require[s] a `BHKS.CutProjectionHypotheses` /
> `RecoveredAtLiftM1` recovery certificate that **no theorem produces from the
> bare loop success** `factorFastCoreWithBound … = some coreFactors`.

## Corrected target (the right ingredients, now located)

Build the per-support **scale-coordinate** certificate
`RecoveredAtLiftM1 core (coreLiftData core B primeData) (factor S) (subset S)`
(Basic:3370 — fields: `monicFactor`, `congr`, `recovered_eq` (scale, no dilate),
`monic_dvd : monicFactor ∣ monicTarget core d.p d.k`) from bare loop success,
then feed the EXISTING core-basis endpoint
`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredM1`
(PartitionRefinement:863) — which takes `∀ S, RecoveredAtLiftM1 …` directly,
over arbitrary `d`, plus `hsupp`/`hfac`/`hfactor`/`hsize`/`hpartition`.
(The 1020 endpoint is an alternative sink; its decomposed witnesses are derivable
from the same `RecoveredAtLiftM1` fields, but 863 is the lower-friction consumer
because it accepts the certificate verbatim.)

Constructor already exists: `recoveredAtLiftM1_of_recovery` (Basic:6050) builds
`RecoveredAtLiftM1` from
  - `c > 0` (cofactor leading coeff),
  - `hcongr : reduceModPow (liftedFactorProduct d S) = reduceModPow monicFactor`,
  - `hmonic_dvd : monicFactor ∣ monicTarget core d.p d.k`,
  - `hhonest : scale ℓf (liftedFactorProduct d S) ≡ scale c factor (mod p^k)`
    (the *honest proportional* congruence — NOT the strong one, which is provably
    false for proper factors with non-unit cofactor lc; see the docstring at
    Basic:6036),
  - `hfactor_prim`, and a Mignotte bound on `scale c factor`.
Per-index Hensel datum `hfac` already exists:
`coreLiftData_liftedFactor_hensel_semantics` (LiftBridge:692).

## Next step (for the next session — supersedes the refined plan)

1. The GENUINELY missing lemma: a producer that, from
   `factorFastCoreWithBound core B primeData … = some coreFactors` +
   `choosePrimeData? core = some primeData`, yields per emitted factor / per
   support the inputs of `recoveredAtLiftM1_of_recovery` (the honest proportional
   congruence + `monic_dvd` + `c` + primitivity + Mignotte bound). Source these
   from the EXECUTABLE recovery soundness around `bhksRecoverClassifiedCore` /
   `bhksIndicatorCandidatesCore?` in HexBerlekampZassenhaus/Basic.lean — that is
   where the scale recovery formula (`hscaled` shape) and the candidate↔selected
   correspondence are certified. Start by reading what
   `bhksRecoverClassifiedCore_success_*` lemmas certify per candidate (esp. any
   monic-target divisibility and the proportional/`primitivePart` recovery), and
   whether a `subset`/`liftedFactorProduct` identification per emitted factor is
   available. The aim is to land the executable→`RecoveredAtLiftM1` bridge that
   FactorSoundness:356 says is missing.
2. With that per-support certificate, rewrite
   `factorFastCore_irreducible_of_liftedTrueSupport` (1558) to: `let d :=
   coreLiftData core k' primeData`; choose its trueSupports as the SCALE-coordinate
   true-support family (NOT `liftedTrueSupports core (toMonicLiftData …)`; that
   family is dilate-coordinate). Likely need a scale-coordinate analogue of
   `liftedTrueSupports` defined via `RecoveredAtLiftM1`, plus the
   partition-count + supportProduct identifications re-proved for it (the
   `factorFastCoreWithBound_some_partition_eq_normalizedFactors_card` (481) and
   `…_some_size_eq_indicators` lemmas must move to the coreLiftData/M1 family).
3. Refine `…_of_recoveredM1` (863) and discharge `hsupp`/`hfac`/`hfactor`/
   `hsize`/`hpartition` over `coreLiftData`.
4. Fix the independent 530 theorem: re-point
   `factorFastCoreWithBound_eq_expected_of_forwardInputs_on_schedule_of_no_prior_recovery`
   (516) and the cap specialization (543) to the coreLiftData schedule (or
   confirm they are dead and delete — check usage first).
5. Then `lake build PartitionRefinement` green; wire FactorSoundness:18.

## Executable-side map (the FIRST ACTION, done — start step 1 here)

What `bhksRecoverClassifiedCore f d = .success candidates` already certifies
(HexBerlekampZassenhaus/Basic.lean, over `d = coreLiftData core k' primeData`):
- `bhksRecoverClassifiedCore_success_dvd` (12862): every candidate ∣ `f` (=core).
- `bhksRecoverClassifiedCore_success_indicatorCandidates` (12893): `hrows`,
  `bhksIndicatorCandidatesCore? f d (equivalenceClassIndicators (projectedRows …))
  = some candidates`, partition non-degenerate.
- product = core.
- Per-indicator recovery formula CONSTRUCTOR:
  `bhksIndicatorCandidateCore?_eq_some_of_scaledCenteredLift` (7558) — candidate i
  = `primitivePart (centeredLiftPoly (reduceModPow (scale ℓf (polyProduct selected))
  p k) (p^k))`, where `selected = bhksIndicatorSelectedFactors d.liftedFactors
  (indicators.getD i)`. This is the forward (build) direction;
  `candidatesOfScaledCenteredLift` (Recovery:2742) is its Mathlib wrapper.

Precise gap to close for `recoveredAtLiftM1_of_recovery` (Basic:6050), per
emitted candidate / support S:
- a `subset : LiftedFactorSubset d` with `liftedFactorProduct d subset =
  Array.polyProduct selected` (subset↔selected identification — needs the
  indicator→subset correspondence the executable uses);
- `monicFactor` with `reduceModPow (liftedFactorProduct d S) = reduceModPow
  monicFactor` and `monicFactor ∣ monicTarget core d.p d.k`. The `monic_dvd` is
  the substantive one: it is "a subset product of the Hensel factors divides
  `monicTarget core` mod p^k", which should fall out of the Hensel-lift invariant
  `monicTarget core ≡ ∏ liftedFactors (mod p^k)` (the `QuadraticMultifactorLiftInvariant`
  used inside `coreLiftData_subset_congr_monicTarget`, Basic:10547);
- the honest proportional congruence `scale ℓf (liftedFactorProduct d S) ≡ scale c
  factor (mod p^k)` with `c` the cofactor leading coeff — derivable from the
  recovery formula above (`primitivePart` strips `c`; the pre-`primitivePart`
  centred lift is `scale c factor` exactly, cf. the `recovered_eq` proof at
  Basic:6070-6101 run in reverse).
Then `factor` primitivity + a Mignotte bound on `scale c factor` (the executable
Mignotte gate `two_mul_…_lt_pow_of_cldCoeffFloor_le`, already used at 1616).

## Blockers

The remaining obligation is mathematical, not mechanical: an executable→
`RecoveredAtLiftM1` per-support scale-coordinate recovery certificate that does
not exist yet (FactorSoundness:356). The refined plan's two proposed sources
(`candidatesOfScaledCenteredLift`; `liftedTrueSupports` descent) BOTH fail —
the first is the wrong granularity (aggregate fold, not per-support), the second
re-hits the #8319 dilate wall. No sorries/axioms were introduced; proof files
were left untouched (HEAD's PartitionRefinement remains the pre-existing
4-error WIP state on this feature branch). I deliberately did not half-migrate
the 1558 body, since doing so without the certificate would only relocate the
type errors and tempt a sorry.
