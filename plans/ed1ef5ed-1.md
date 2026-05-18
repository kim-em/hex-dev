## Current state

The /replan agent closed #4639 ("relax three exhaustive wrappers to
primitive + pos-leading core") asking the planner to refile its
prerequisite chain as sub-issues of #4626 (closed).  Three direct
prerequisites for the executable layer have already been filed and
landed or are queued:

* #4866 — `recombineScaledExhaustive` + structural invariants
  (landed via PR #4872).
* #4869 — `scaledRecombinationSearchMod_product` and
  `recombineScaledExhaustive_product` (functionally unblocked by
  #4866).
* #4870 — swap `Hex.exhaustiveCoreFactorsWithBound` to call
  `recombineScaledExhaustive` (blocked on #4866 + #4869).
* #4875 — scaled membership wrapper
  `exhaustiveCoreFactorsWithBound_mem_of_scaledRecombinationSearchMod_some`
  (blocked on #4866 + #4870).

This issue is the **final wrapper-relaxation successor of #4639**
that the /replan triage on #4640 explicitly requested
(see [#4640 closure comment](https://github.com/kim-em/hex/issues/4640#issuecomment-4474054430),
item 2):

> Relax the three top-level wrappers in
> `HexBerlekampZassenhausMathlib/Basic.lean`
> (`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence`,
> `exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`,
> `factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`)
> from `(hcore_monic)` to `(hcore_primitive, hcore_lc_pos)`, chaining
> through the new scaled membership wrapper plus the #4648 primitive
> wrapper.

The relaxed substrate already exists on `main`:

* `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core`
  at `HexBerlekampZassenhausMathlib/Basic.lean:12697` (landed via
  #4849, the #4648 primitive recombination wrapper).  This is the
  primitive + positive-leading sibling of the
  `_of_liftedFactorSubsetPartition` form used by the current monic
  wrappers (line 12796), routing through
  `Hex.scaledRecombinationSearchModAux` and the scaled candidate.
* The three target wrappers at lines 12761 / 12839 / 13233 still take
  `hcore_monic : Hex.DensePoly.Monic core` and chain internally
  through the unscaled
  `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
  + the unscaled membership wrapper
  `exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some`.

After #4870 (call-site swap) lands, the unscaled membership wrapper
ceases to apply at the relaxed call site because the executable body
unfolds to the scaled recombination; the scaled sibling from #4875 is
the replacement.

depends-on: #4875

(#4875 transitively depends on #4866 + #4870, so this issue's full
prerequisite closure is #4866 → #4869 → #4870 → #4875 → here.)

## Deliverables

In `HexBerlekampZassenhausMathlib/Basic.lean`, relax the three
wrappers' boundary hypothesis from
`(hcore_monic : Hex.DensePoly.Monic core)` to the pair
`(hcore_primitive : Hex.ZPoly.Primitive core)
 (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)`, and rewire
their proofs through the relaxed substrate.

1. **`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence`**
   (line 12761): replace the internal
   `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
   call (line 12796) with
   `recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core`
   (line 12697). Replace the `exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some`
   call (line 12809) with the scaled sibling from #4875,
   `exhaustiveCoreFactorsWithBound_mem_of_scaledRecombinationSearchMod_some`.
   The `recombinationSearchMod` → `scaledRecombinationSearchMod`
   bridging shape mirrors line 12802-12806 but at the scaled flavour.
2. **`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`**
   (line 12839): swap `hcore_monic` for `hcore_primitive, hcore_lc_pos`,
   forward those hypotheses to the call to
   `exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence`
   at line 12897.
3. **`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`**
   (line 13233): swap `hcore_monic` for `hcore_primitive, hcore_lc_pos`,
   forward those hypotheses to the call to
   `exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`
   at line 13281.

If consumers in `HexBerlekampZassenhausMathlib/IntReductionMod.lean`
(the four downstream call sites in
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux`
near lines 1589/1599/1606/1611/1644 — see #4640 audit) still supply
`hcore_monic`, retain monic-compatibility specialisations under a
clearly named `_of_monic_core` form (or trivially derive
`hcore_primitive` + `hcore_lc_pos` from monicness in the consumer).
Either approach is acceptable; the umbrella-side drop of `hcore_monic`
Gap 1 is a separate successor sub-issue (refile of #4640) and not in
scope here.

Do not introduce `sorry`, `axiom`, `native_decide`, `TODO`, or
`FIXME`.

## Library placement

* **SPEC §:** `SPEC/Libraries/hex-berlekamp-zassenhaus-mathlib.md` —
  exhaustive-arm coverage and irreducibility bridge.
* **Mathlib use:** yes. All changes live in
  `HexBerlekampZassenhausMathlib/Basic.lean`.

## Context

* /replan triage of #4640 ([comment 4474054430](https://github.com/kim-em/hex/issues/4640#issuecomment-4474054430))
  enumerated this issue and the umbrella drop as the two remaining
  unfiled successors of the #4639 chain.
* The relaxed substrate `_of_primitive_pos_lc_core` was landed by
  #4849 (PR also #4849) for the per-factor recombination boundary.
  See its docstring at line 12690-12695 for the design intent.
* The scaled candidate machinery (cover-at-min, prefix-none,
  exact-quotient) is the proof core; downstream wrappers chain
  through it via the substrate functions named above.

## Verification

* `lake build HexBerlekampZassenhausMathlib.Basic`
* `lake build HexBerlekampZassenhausMathlib`
* `python3 scripts/check_dag.py`
* `git diff --check`
* `rg -n "sorry|axiom|native_decide|TODO|FIXME" HexBerlekampZassenhausMathlib/Basic.lean`
  shows no new entries on the diff against `origin/main`.

## Out of scope

* The umbrella-side drop of `hcore_monic` Gap 1 from
  `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData`
  in `HexBerlekampZassenhausMathlib/IntReductionMod.lean` (refile of
  #4640's deliverables 1–6). Successor sub-issue.
* Relaxing `reassemblyExpansionComplete_exhaustive_of_ne_zero`
  (`IntReductionMod.lean:3422`) to drop `hcore_monic` — only required
  if the umbrella drop reaches the `IntReductionMod` call site.
* BHKS Theorem 5.2 / directive #2567.
* Editing `SPEC/`, top-level `PLAN.md`, or `AGENTS.md`.
