## Current state

PR #4516 (merged commit `942e2d3d`) landed
`liftedFactorSubsetPartition_prefix_none` at
`HexBerlekampZassenhausMathlib/Basic.lean:5791`, completing the
prefix-none discharge for the recursive recombination assembler in
#4301. Both that theorem (L5807-5808) and the upstream wrapper
`liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches`
(L3291-3296) take `hlocal_nodup : localFactors.Nodup` as a
hypothesis, with docstrings that explicitly defer the discharge to
"a Hensel-coprimality fact at the recombination call site
(`liftedFactor d` injective on the J-filter index list)" —
see L3281-3286 and L5784-5789.

The progress note `progress/20260516T162208Z_083008d1.md` flags
the matching shim — a thin helper that, given injectivity of
`liftedFactor d` over the indices in `J`, derives
`localFactors.Nodup` from the matching predicate — as a separable
sub-task. This issue extracts that helper so #4301's consumer can
focus on producing the injectivity hypothesis itself.

The matching predicate is defined at L2268-2272:

```lean
def LiftedFactorListMatches (d : Hex.LiftData) (J : LiftedFactorSubset d)
    (localFactors : List Hex.ZPoly) : Prop :=
  localFactors =
    ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ J)).map
      (liftedFactor d)
```

so `Nodup` reduces to `Nodup` of the filter pre-image (which is a
`Nodup`-preserving filter of `List.finRange`) combined with
injectivity of `liftedFactor d` on the indices that survive the
filter — i.e., the elements of `J`.

## Deliverables

1. In `HexBerlekampZassenhausMathlib/Basic.lean`, add a top-level
   helper next to `LiftedFactorListMatches.length_eq_card`
   (around L2302). Exact statement is the author's choice; one
   reasonable shape:

   ```lean
   theorem LiftedFactorListMatches.nodup_of_injOn
       {d : Hex.LiftData} {J : LiftedFactorSubset d}
       {localFactors : List Hex.ZPoly}
       (h : LiftedFactorListMatches d J localFactors)
       (hinj : Set.InjOn (liftedFactor d) (J : Set (LiftedFactorIndex d))) :
       localFactors.Nodup
   ```

   Variants are acceptable if they integrate more cleanly with the
   surrounding API (e.g., taking `Function.Injective (liftedFactor d)`
   when the consumer can supply it that strongly, or restating in
   terms of `liftedSubsetSelectedList d J` via the existing
   `LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList` bridge).
   Pick whichever signature minimises the consumer-side discharge in
   #4301.

2. Add a short docstring naming both consumer call sites
   (`liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` and
   `liftedFactorSubsetPartition_prefix_none`) and citing the
   injectivity premise as a Hensel-coprimality fact, mirroring the
   existing docstring language at L3281-3286.

3. Do not extend or weaken the partition predicate
   `LiftedFactorSubsetPartition`. The discharge of the injectivity
   premise from partition data plus Hensel coprimality is intentionally
   the consumer's responsibility in #4301; this issue stops at the
   pure list-level shim.

## Context

- `LiftedFactorListMatches` and the iff bridge to
  `liftedSubsetSelectedList`:
  `HexBerlekampZassenhausMathlib/Basic.lean:2268-2282`.
- `LiftedFactorListMatches.length_eq_card` (the existing sibling
  consumer of the matching predicate, for placement reference):
  `HexBerlekampZassenhausMathlib/Basic.lean:2302-2307`.
- Consumer docstrings that flag the injectivity premise:
  `HexBerlekampZassenhausMathlib/Basic.lean:3281-3286` and
  `HexBerlekampZassenhausMathlib/Basic.lean:5784-5789`.
- Progress note flagging this as a separable sub-task:
  `progress/20260516T162208Z_083008d1.md`.

## Out of scope

- Discharging the injectivity premise itself (whether from the
  partition predicate's `pairwise_disjoint` / `unique_up_to_associated`
  fields, from Hensel-side `henselLiftData` invariants, or by
  extending the partition predicate). That belongs to #4301 or a
  follow-up planner sub-issue if the consumer flags it.
- Replacing or refactoring the existing `hlocal_nodup` hypothesis on
  `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` or
  `liftedFactorSubsetPartition_prefix_none`. Those stay as-is; the
  helper supplies a clean shim for downstream callers to chain.
- Any change to `LiftedFactorListMatches`, `liftedSubsetSelectedList`,
  `liftedSubsetMask`, or `liftedFactor` definitions.

## Verification

- `lake build HexBerlekampZassenhausMathlib.Basic`
- `lake build HexBerlekampZassenhausMathlib`
- `python3 scripts/check_dag.py`
- `git diff --check`
- No new `axiom`, `native_decide`, `TODO`, `FIXME`, or theorem-level
  `sorry`. Pre-existing `sorry` count at L160 / L239 (= 2) on
  `HexBerlekampZassenhausMathlib/Basic.lean` must be unchanged.
