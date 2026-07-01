# Issue #8510 bound-parameterized classical irreducibility

## Accomplished

Surfaced the abstract coefficient-bound machinery for the classical
recombination search's per-factor irreducibility, so the hybrid residual
arm can run the search on `core = (normalizeForFactor f).squareFreeCore`
at search bound `B = defaultFactorCoeffBound f` without a
`defaultFactorCoeffBound core ≤ defaultFactorCoeffBound f` monotonicity
lemma (which does not exist and is not needed: `core ∣ f`, so Mignotte
bounds every divisor of `core` by `defaultFactorCoeffBound f`).

In `HexBerlekampZassenhausMathlib/Basic.lean`:
- Added public `RecoveredSmartSearch.covers_of_bound` and
  `RecoveredSmartSearch.trustworthyNone_of_bound`, surfacing the private
  `smartAux_covers_of_bound` / `smartAux_none_budget_zero` with the
  coefficient bound `B'`, `hcore_lc_le`, `hvalid`, and `2 * B' < d.p^d.k`.
- Rewrote `RecoveredSmartSearch.covers` / `.trustworthyNone` as the
  `B' = defaultFactorCoeffBound core` specializations of the new lemmas
  (semantics unchanged).

In `HexBerlekampZassenhausMathlib/IntReductionMod.lean`:
- Renamed `classicalCoreFactorsWithBound_factor_irreducible_of_bound`
  to `_of_validBound`, parameterizing the coefficient bound `B'` with
  `hcore_lc_le` / `hvalid` and precision `2 * B' < …`.
- Kept `_of_bound` as a thin wrapper specializing at
  `B' = defaultFactorCoeffBound core`, so `classicalCoreFactorsWithBound_factor_irreducible`
  (natural-bound form) is unchanged.
- Added `classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`:
  the `B' = defaultFactorCoeffBound f` specialization giving
  `∀ g ∈ cf.toList, Hex.ZPoly.Irreducible g`, discharging validity via
  `defaultFactorCoeffBound_valid f ∘ zpoly_dvd_trans ∘ squareFreeCore_dvd_self`
  and precision via `exhaustiveLiftBound_precision`.

`lake build HexBerlekampZassenhausMathlib` is green; no new `sorry`/`axiom`.
The only remaining `sorry` is the pre-existing `factor_irreducible_of_nonUnit`
(the eventual #8414 consumer).

## Current frontier

The two ingredients for the classical residual arm are now both
available: this issue's per-factor irreducibility and #8511's
`reassemblyExpansionComplete` side condition.

## Next step

#8414 residual arm consumes
`classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`
together with #8511's completeness lemmas to drop the
`factor_irreducible_of_nonUnit` classical-branch `sorry`.

## Blockers

None.
