## Current state

`HexBerlekampZassenhausMathlib/Basic.lean` exposes the public-layer
`_some_factor_associated_of_liftedFactorSubsetPartition` recombination
search theorems in three shape families:

- **Monic**:
  `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
  (around line 14781 on `origin/main`) — no `_of_bound` sibling, currently
  unwraps the monic `_some_and_covers_` aux.
- **Unscaled primitive (pos LC)**:
  `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound`
  — exists, dispatches into the scaled `_of_bound` variant.
- **Scaled primitive**:
  `scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
  — exists at the abstract bound layer.

PR #5192 just added the internal aux
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`
(monic case, abstract bound `B'`) and rewired the existing
`_some_and_covers_` as a thin wrapper. The public monic
`_some_factor_associated_` consumer was *not* updated and still calls the
thin wrapper rather than the new `_of_bound` aux, leaving the trio of
`_of_bound` `_some_factor_associated_` public siblings incomplete on the
monic side.

The scaled variant
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
(around line 14826 on `origin/main`) is the structural precedent for the
new monic sibling — same body shape (`obtain ⟨result, hresult, hcovers⟩ :=
_some_and_covers_..._of_bound …; exact ⟨result, hresult,
hcovers factor hfactor_irr hfactor_dvd_target⟩`).

## Deliverables

1. Add
   `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
   to `HexBerlekampZassenhausMathlib/Basic.lean`, inserted immediately
   *before* the existing public
   `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`.
   Signature mirrors the existing public monic theorem with three changes:
   - Replace the concrete precision hypothesis
     `(hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)`
     with the abstract bound triple:
     `(B' : Nat)`,
     `(hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')`,
     `(hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')`,
     `(hprecision : 2 * B' < d.p ^ d.k)`.
   - Keep the monic-side hypotheses (`hcore_monic`, `htarget_monic`)
     unchanged.
   - Body: thin wrapper around
     `recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`
     followed by `⟨result, hresult, hcovers factor hfactor_irr
     hfactor_dvd_target⟩`, structurally identical to the existing
     scaled `_some_factor_associated_..._of_bound` body (around
     line 14826).

2. Rewire the existing
   `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
   as a thin delegator into the new `_of_bound` sibling:
   - Pass `B' := Hex.ZPoly.defaultFactorCoeffBound core`.
   - Discharge `hcore_lc_le` via
     `defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne`.
   - Discharge `hvalid` via `defaultFactorCoeffBound_valid core hcore_ne`.
   - Forward `hprecision` as the abstract-bound `hprecision : 2 * B' <
     d.p ^ d.k` consumer.
   This pattern is identical to how the scaled wrapper at line 14728 on
   `origin/main` delegates into its `_of_bound` sibling.

## Context

- `progress/20260519T010726Z_cf8429c2.md` — PR #5192 progress note, describes
  the internal monic `_of_bound` substrate now in place.
- `progress/20260518T235744Z_af7b4e69.md` — explicitly identifies "the
  natural follow-up is the next layer up" for the analogous unscaled-primitive
  case (which is already done at this surface); this issue closes the
  parallel gap on the monic side.
- The body of the new theorem is **not** a re-induction: the fuel induction
  is already in
  `recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`.
  The new public theorem just extracts the per-factor existential via
  `hcovers factor hfactor_irr hfactor_dvd_target`.

## Verification

- `lake build HexBerlekampZassenhausMathlib.Basic`. The file has known
  pre-existing `whnf` heartbeat timeouts in this file (lines around 4900–6300
  and kernel "unknown constant" errors at the tail) which are environment-
  specific; verify by `git stash` baseline-compare that your change does not
  introduce any new errors or warnings.
- `python3 scripts/check_dag.py`.
- `git diff --check`.
- `git diff origin/main -- HexBerlekampZassenhausMathlib/Basic.lean | rg
  -nE '^\+.*(sorry|axiom|native_decide|TODO|FIXME)'` — must be empty.
- No downstream call-site changes are required for this PR. Existing
  call sites of
  `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
  continue to type-check through the rewired thin wrapper.

## Out of scope

- Migrating any specific caller to the new `_of_bound` form. The wrapper
  remains the canonical entry point for `defaultFactorCoeffBound`-based
  callers. Migration of any consumer that has its own abstract bound in
  hand is a separate follow-up.
- The unscaled-primitive `_some_and_covers_` `_of_bound` sibling. The
  unscaled-primitive `_some_factor_associated_` already dispatches into
  the scaled `_of_bound` variant, so no parallel auxiliary is needed at
  this surface.
