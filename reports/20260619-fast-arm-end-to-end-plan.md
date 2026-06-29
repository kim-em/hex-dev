# End-to-end plan: closing `factor_irreducible_of_nonUnit` (separation-free)

Verified against `origin/main` + two adversarial second-opinion rounds
(`reports/20260619-codex-fastsoundness-plan-round{1,2}.md`). The headline theorem
is reachable **without** the BHKS bad-vector separation (`L'=W` / #6779); that
separation belongs only to the *optional* "fast path always taken" guarantee.

## The function

```
factor f       = (factorFast f).getD (factorSlow f)
factorSlow f   = (factorSlowModular f).getD (factorSlowTrial f)
```
`factorFast : ZPoly → Option Factorization` may return `none` (slow fallback runs).

## Decomposition

- **(A) Fast soundness** — `factorFast f = some φ ⟹ φ` is the irreducible
  factorisation. *The remaining work.*
- **(C) Slow soundness** — `factorSlow` correct. **Already proved.**
- **(B) Fast completeness** ("always taken") — `factorFast f ≠ none`. **Optional**,
  performance-only; A+C already make `getD` correct in both branches. The
  separation `L'=W` (#6779, bad-vector resultant/Hadamard) lives **here**, OFF the
  correctness path.

## Why A is separation-free (verified)

`factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`
(`PartitionRefinement.lean:591`): from `(trueSupports, success, hcut, hsize,
hpartition)` proves every emitted factor irreducible, via
`count_eq_of_cut` = `count_ge` (from `W ⊆ L'` ALONE,
`supportPartitionByMinColumn_length_le_bhksEquivalenceClassIndicators_size`) +
`count_le` (from `product = core`) → UFD count→irreducible. The executable output
connects **only by cardinality**, never identity, so no `L'=W`.
`hcut : CutProjectionHypotheses L trueSupports` (= `W ⊆ L'`) is built from the
**true** factors by `cutProjectionHypotheses_of_trueFactors` (`Lattice.lean:2132`)
from `TrueFactorCLDVectorData` + `TrueFactorCLDTightNormBound` — true-factor
certificates, not the executable recovered partition.

The cardinality chain (closes without emitted↔true identification):
`#emitted = #L'-indicators` (hsize); `#irreducibles = #trueSupports` (hpartition);
`#trueSupports ≤ #L'-indicators` (W⊆L'); `#emitted ≤ #irreducibles` (count_le)
⟹ all equal.

## Remaining obligations (where each lives)

1. **A1 — true-factor data over `trueSupports`** (HexBZMathlib/Basic.lean + Lattice.lean)
   - `trueSupports := liftedTrueSupports core d` (Basic.lean:3586, EXISTS:
     supports of the true factors; partition of `{1..r}`).
   - `hpartition`: `#trueSupports = #normalizedFactors` — the `liftedTrueSupports`
     `ncard` bijection (Basic.lean:14328, EXISTS/near).
   - per-`S_j`: `TrueFactorCLDVectorData` + `TrueFactorCLDTightNormBound` via the
     **RecoveredLift** route (NOT the vacuous raw-product `TrueFactorLift`):
     `recovered_eq` = `dilate(lc)(centeredLiftPoly(supportProduct S_j)) = g_j`,
     provable from Hensel-correspondence selection + centered-lift uniqueness at
     the accepted precision (Mignotte/CLD-floor). Tight-norm via the landed
     aggregate-tail discharge (#7887) + the gate's `hsep`.
2. **A2 — `hcut` (W⊆L')**: `cutProjectionHypotheses_of_trueFactors` over A1.
   Infra landed (#7884 period-corrected vector, #7887 aggregate-tail).
3. **Precision alignment** (Basic.lean/PartitionRefinement.lean): strengthen
   `factorFastCoreWithBound_some_indicatorCandidates` to EXPOSE the gate fact
   `k ≥ cldCoeffFloor core` (currently discarded), so A1's recovery data, `hcut`,
   and `hsize` all refer to the SAME accepted `L`. The gate (#7959) guarantees it;
   the extractor must carry it.
4. **hsize**: `bhksIndicatorCandidates?_size_eq` + the extractor. LANDED.
5. **A4 — assembly**: `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_cut`
   with A1+A2+A3. LANDED endpoint. (PartitionRefinement.lean)
6. **A5 — capstone** (FactorSoundness.lean:18): `factor = fast.getD slow`; `some`
   → A4, `none` → C. Thin. Also: non-association strengthening (currently
   syntactic distinct-key; FactorSoundness.lean:38).

## (B) optional, deferred

Fast completeness ("always taken"): separation `L'=W` at cap (#6779) + recovery
termination ⟹ `factorFast ≠ none`. Not required for the headline theorem.

## Net

The headline theorem is **one substantive obligation (A1) plus plumbing** away,
all separation-free. The infra (`_of_cut`, `_of_trueFactors`, `liftedTrueSupports`,
the gate, the period-aware/aggregate-tail discharge, slow soundness) is landed.
