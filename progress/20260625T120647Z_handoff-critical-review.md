**Accomplished**

Reviewed `progress/20260625T120000Z_foundation-verified-1558-isolated.md` and
`progress/RESUME_PROMPT.md` against the current Lean source. Verified the target
build state with `lake build HexBerlekampZassenhausMathlib.PartitionRefinement`:
it fails with exactly the three documented errors at lines 1606, 1678, and 1681,
all stale `coreLiftData`/`toMonicLiftData` mismatches inside
`factorFastCore_irreducible_of_liftedTrueSupport`.

Confirmed the `RecoveredAtLiftM1.monic_dvd` removal is consistent with the M1 cut
chain: `cutProjectionHypotheses_of_recoveredM1` routes through
`congr_logDeriv_bridge_of_recoveredM1`, `exists_scale_congr_factor_of_recoveredM1`,
and `RecoveredAtLiftM1.candidate_eq`, none of which consume a divisibility field.

Found major handoff risks: the M1 endpoint requires `Hex.choosePrimeData? core =
some primeData`, while the current 1558 theorem and M2 descent use
`Hex.ZPoly.toMonicPrimeData? core = some primeData`; the docs' "same shared
ModPFactorSubset family" claim is therefore too strong. Also,
`representsModP_correspondent` explicitly warns that the monic correspondent's
mod-p subset is not a prescribed subset of the original factor because dilation is
not monic-modular-image invariant, making the proposed `gf ↔ monicTarget factor`
bridge a serious unproved premise.

**Current frontier**

The handoff documents should be corrected before a fresh worker receives them.
The safe M1 plan likely needs a direct core-prime-data route, or an explicit
theorem relating the two prime-data selections and the corresponding mod-p
subsets. It should not tell the next worker to reuse the M2 descent as if it were
coordinate-agnostic.

**Next step**

Update `RESUME_PROMPT.md` to highlight the `choosePrimeData? core` versus
`toMonicPrimeData? core` mismatch, require proving the `hselected` source first,
and replace the optimistic `gf ↔ monicTarget factor` wording with a hard
feasibility check. Also mention that
`factorFastCoreWithBound_some_size_eq_indicators` is still specialized to
`toMonicLiftData`; the generic `BHKS.size_eq_indicators_of_candidates` may need a
coreLiftData wrapper.

**Blockers**

No files under the proof path were edited in this review. The blocker is
documentary/planning accuracy: the current resume prompt can send the next worker
down an M2-descent route that the source itself flags as unsound for prescribed
mod-p subsets.
