# M1 recovery certificate: foundation lemma landed + path de-risked

## Accomplished

**Corrected the migration plan (premise check, corroborated by Codex) AND
started implementing the corrected version with one verified lemma landed.**

The "REFINED PLAN" (in `20260625T000000Z_…`) is wrong: see
`20260625T070000Z_partitionrefinement-premise-corrected.md` for the full
evidence. Short version: the 1020/863 M1 endpoints need a SCALE-coordinate
per-support `RecoveredAtLiftM1` certificate; the abstract
`liftedTrueSupports core (coreLiftData …)` family is DILATE-coordinate
(`RecoveredAtLift`, Basic:2378) and re-hits #8319. `dilate` (coeff i × cᶦ;
HexPolyZ/Basic.lean:65) and `scale` (whole-poly × constant) are genuinely
different ops, confirmed from source. The whole BHKS completeness layer
(`liftedTrueSupports`, `LiftedFactorSubsetPartition`, the partition-count, all
producers) is M2/dilate-only — the M1/scale path needs fresh analogues.

**LANDED + VERIFIED (executable layer, green, 148s build):**
`bhksIndicatorCandidateCore?_eq_some_elim` (HexBerlekampZassenhaus/Basic.lean,
right after `bhksIndicatorCandidateCore?_dvd` ~7069). It is the inverse of
`bhksIndicatorCandidateCore?_eq_some_of_scaledCenteredLift`: from a successful
indicator candidate it extracts the selected lifted-factor subset, the exact M1
scale-recovery formula
`candidate = normalizeFactorSign (primitivePart (centeredLiftPoly (reduceModPow
(scale ℓf (polyProduct selected)) p k) (liftModulus d)))`, and the cofactor
`exactQuotient? f candidate = some quotient`. This is the per-indicator soundness
surface the `RecoveredAtLiftM1` certificate harvests. `lake build
HexBerlekampZassenhaus.Basic` is GREEN (492 jobs) — no sorry, no axiom.
(NOT committed — left as verified WIP per "commit only when asked".)

## Path de-risked: the certificate's ingredients all exist

`recoveredAtLiftM1_of_recovery` (Basic:6050) builds `RecoveredAtLiftM1 core d
factor S` from `(c>0, hcongr, hmonic_dvd, hhonest, hfactor_prim, Mignotte)`.
Mapping each input to an existing producer:
- `factor` := the emitted candidate; `hfactor_prim` from
  `bhksIndicatorCandidatesCore?_primitive` (exec Basic:7341).
- subset S + `liftedFactorProduct d S = polyProduct selected`:
  `polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct` (Basic:5635) +
  the indicator↔support bridges
  `bhksIndicatorSelectedFactors_expectedIndicatorArrayOfSupports`
  (Recovery:1573), `selectedFactorsOfMembers_polyProduct` (Recovery:1234).
- `monicFactor` := `polyProduct selected` (then `hcongr` is `rfl`/`reduceModPow`).
- `hmonic_dvd : monicFactor ∣ monicTarget core d.p d.k`: from the Hensel
  invariant `henselLiftData_liftedFactorProduct_univ_congr_core` (Basic:9802) +
  `liftedFactorProduct_eq_mul_sdiff_of_subset` (Basic:9724) — a subset product
  divides the full product ≡ monicTarget core (coreLiftData lifts monicTarget
  core directly, no dilation).
- `hhonest : scale ℓf (liftedFactorProduct d S) ≡ scale c factor`: the
  pre-`primitivePart` centred lift is `scale c factor` exactly (c = cofactor lc);
  derive from the extraction formula + `centeredLiftPoly_congr_self` (Basic:3422),
  reversing the `recovered_eq` proof at Basic:6070-6101.
- Mignotte: the exec gate `two_mul_defaultFactorCoeffBound_core_lt_pow_of_cldCoeffFloor_le`
  (used at PartitionRefinement:1616).

## Next step

1. Write the Mathlib certificate lemma (in Mathlib Basic.lean, near
   `coreLiftData_subset_congr_monicTarget` Basic:10547, or LiftBridge): from
   `factorFastCoreWithBound … = some coreFactors` + `choosePrimeData? = some
   primeData`, produce per emitted factor a `RecoveredAtLiftM1 core
   (coreLiftData core B primeData) factor subset`, using the landed
   `bhksIndicatorCandidateCore?_eq_some_elim` + the bridges above +
   `recoveredAtLiftM1_of_recovery`. (Mathlib Basic builds are slow — minimize
   iterations; develop the sub-facts as separate small lemmas first.)
2. Build the M1 true-support family (scale-coordinate sibling of
   `liftedTrueSupports`, defined via `RecoveredAtLiftM1`) + its partition-count
   lemma (sibling of `supportPartitionByMinColumn_length_eq_normalizedFactors_card`
   PartitionRefinement:226). This is the larger remaining piece. Investigate
   whether the supports transport from the M2 family (both lifts share the same
   `primeData.factorsModP`, so support index sets coincide up to the
   `liftedFactors.size = factorsModP.size` identification) — a transport would
   reuse the existing M2 partition count instead of re-deriving it.
3. Feed the 863 endpoint
   `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_recoveredM1`
   (PartitionRefinement:863) with the certificate; discharge hsupp (via the
   indicator↔support product bridges), hfac (`coreLiftData_liftedFactor_hensel_semantics`
   LiftBridge:692), hfactor (the `exactQuotient?` cofactor), hsize, hpartition.
4. Rewrite `factorFastCore_irreducible_of_liftedTrueSupport` (1558) to use the
   above over `coreLiftData`; fix the independent 530 schedule theorem; build
   PartitionRefinement green; wire FactorSoundness:18.

## M2→M1 transport probe: CONFIRMED VIABLE (avoids re-deriving the layer)

Probed whether the M1 partition count can transport from the existing M2 result
instead of re-deriving `LiftedFactorSubsetPartition` at `coreLiftData`. Result:

- The dilate machinery (`LiftedFactorSubsetPartition` Basic:3882,
  `ncard_eq_normalizedFactors_card` Basic:15195,
  `supportPartitionByMinColumn_length_eq_liftedTrueSupports_ncard`
  PartitionRefinement:198) is generic over `d` BUT defined via
  `RepresentsIntegerFactorAtLift` = dilate `RecoveredAtLift`. It is inhabited
  only at `toMonicLiftData` (dilate recovery at `coreLiftData` is the wrong/
  uninhabited coordinate). So it CANNOT be reused at `coreLiftData` directly.
- BUT the COUNTING PRIMITIVE
  `supportPartitionByMinColumn_length_eq_ncard_of_partition`
  (PartitionRefinement:208) is fully GENERIC: given any `Set (Set (Fin r))` with
  cover / pairwise-eq-on-intersection / nonempty, it yields `length = ncard`.
  Not tied to `liftedTrueSupports`.
- `liftedSubsetOfModPSubset primeData d hsize S₀ = S₀.map (embedding)`
  (Basic:2281) — the SAME `ModPFactorSubset primeData` subset retyped to
  `Fin d.liftedFactors.size`. It is injective (Basic:2301) and preserves
  subset/disjointness (Basic:2311/2327). Both `coreLiftData` and
  `toMonicLiftData` use the SAME `primeData.factorsModP`, so both support
  families are images of the SAME modP true-support family under
  structurally-identical injective maps.

**Conclusion — the transport route (much smaller than re-deriving the layer):**
1. Define the M1 `trueSupports` for the 863 endpoint as the image of the shared
   modP true-support family under `liftedSubsetOfModPSubset primeData
   (coreLiftData …)` (NOT a new dilate partition).
2. Get its cover/disjoint/nonempty by transporting from the modP family (shared
   with M2; injectivity + subset/disjoint-iff lemmas), then apply the generic
   `supportPartitionByMinColumn_length_eq_ncard_of_partition` for length = ncard,
   and ncard = (modP family).ncard = normalizedFactors card (the M2 chain already
   proves the modP count via the injective image — reuse
   `supportPartitionByMinColumn_length_eq_normalizedFactors_card_of_toMonicPrimeData`
   PartitionRefinement:260 as the source of the count).
3. Per support (= `liftedSubsetOfModPSubset … S₀`), produce `RecoveredAtLiftM1`
   from the executable scale recovery (landed extraction lemma) +
   `recoveredAtLiftM1_of_recovery` + the Recovery indicator↔subset bridges.
4. Feed the 863 endpoint; the `hsupp`/`hfac`/`hfactor`/`hsize`/`hpartition`
   leaves discharge over the modP-image family.

This reuses ALL the existing M2 count infrastructure via the shared modP family;
the genuinely new work is the per-support `RecoveredAtLiftM1` certificate plus
the modP-image family's cover/disjoint/nonempty transport.

## CRITICAL FINDING: the M1 endpoint's `monic_dvd` is vestigial + undischargeable as stated

While assembling the certificate I hit the real nub. `recoveredAtLiftM1_of_recovery`
(Basic:6050), `cutProjectionHypotheses_of_recoveryData` (CLDColumnBound:2774), and
the `RecoveredAtLiftM1` structure (Basic:3370) all require
`hmonic_dvd : monicFactor ∣ Hex.ZPoly.monicTarget core d.p d.k` — EXACT ℤ[x]
divisibility. This is **not dischargeable** for proper factors:
- `monicTarget core = reduceModPow (scale ℓc⁻¹ core) p k` is a centered-mod-p^k
  reduction; its exact ℤ[x] factorisation does NOT track `core`'s factors.
- The natural `monicFactor` choices (the subset product `liftedFactorProduct d S`,
  or `monicTarget factor`) divide `monicTarget core` only **mod p^k**, never
  exactly (the Hensel invariant `…univ_congr_core` Basic:9802 is a `congr`, not an
  equality; a subset product exactly divides only the full product, which is `≡`
  not `=` `monicTarget core`).
- Contrast the M2 path: there `monic_dvd : monicFactor ∣ (toMonic core).monic`,
  and `(toMonic core).monic` DOES have an exact ℤ[x] factorisation matching
  `core`'s factors (via `dilate`), so it discharges (Basic:6595, 10322). The M1
  endpoint mirrored the field against the wrong target (`monicTarget core`).

BUT `monic_dvd` is **never consumed on the M1 cut path**. Traced:
`cutProjectionHypotheses_of_recoveredM1` → `congr_logDeriv_bridge_of_recoveredM1`
(CLDColumnBound:2459) → `exists_scale_congr_factor_of_recoveredM1` (Basic:3441) →
`RecoveredAtLiftM1.candidate_eq` (Basic:3394) — all use only the `congr` and
`recovered_eq` fields. The only `monic_dvd` consumers (Basic:6595, 2835, 3146,
14705) are the M2/dilate / `RepresentsIntegerFactorAtLift` path, NOT the M1 cut.
So on the M1 path `monic_dvd` is dead weight that nonetheless blocks construction.

**THE FIX (the actual unblock — supersedes "build the certificate as-is"):**
Refactor the M1 recovery-data→cut path to not require `monic_dvd`:
- Introduce a `monic_dvd`-free recovery package (just `monicFactor`, `congr`,
  `recovered_eq`) — or weaken `RecoveredAtLiftM1` by dropping `monic_dvd` and
  re-proving its M2 consumers from the M2 carrier instead.
- Add `congr_logDeriv_bridge` + `cutProjectionHypotheses_of_recoveryData`
  variants that take the lighter package (drop the `hmonic_dvd` hypothesis;
  everything downstream already ignores it).
- Then the certificate's per-support inputs are ALL dischargeable from the
  executable recovery: `recovered_eq` from the landed
  `bhksIndicatorCandidateCore?_eq_some_elim` (the M1 scale formula) +
  `RecoveredAtLiftM1.candidate_eq` shape; `congr`/`hhonest` from
  `coreLiftData_subset_congr_monicTarget` (Basic:10547) +
  `honestCongr_of_product_congr_monicTarget` (Basic:20403); the Mignotte coeff
  bound from the existing gate. No exact `monicTarget core` divisibility needed.

This is a focused refactor of CLDColumnBound.lean (slow Mathlib build) — it is the
genuine remaining obstruction, and it is a DESIGN bug in the never-yet-fed M1
endpoints, not new mathematics. After it, the transport (above) + the extraction
lemma (landed) close the path.

## Blockers

The remaining work is the M1/scale completeness layer (certificate + true-support
family + partition count). It is now fully mapped with all reusable producers
located, and the executable foundation is landed and verified. Mathlib Basic.lean
build times are the main friction (develop sub-lemmas in isolation). No
sorries/axioms introduced; the one code change (exec extraction lemma) is green.
