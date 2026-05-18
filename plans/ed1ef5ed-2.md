## Current state

The /replan triage on #4640
([comment 4474054430](https://github.com/kim-em/hex/issues/4640#issuecomment-4474054430))
explicitly requested three planner follow-ups after closing #4640
("HO-1 substrate (#4626 sub): drop hcore_monic Gap 1 from #4561
exhaustive umbrella"):

1. ✅ Scaled membership wrapper — filed as #4875.
2. ✅ Wrapper relaxation in `HexBerlekampZassenhausMathlib/Basic.lean`
   — filed as #4879.
3. ❌ **This issue.** Refile #4640's umbrella-side drop deliverables
   (1–6) once (2) is filed; depends on the wrapper-relaxation
   issue.

The target umbrella is
`factor_exhaustive_branch_entry_irreducible_of_choosePrimeData` in
`HexBerlekampZassenhausMathlib/IntReductionMod.lean:3573`.  Its
docstring (lines 2900-2935 region) flags `hcore_monic` as **Gap 1**:

> Gap 1 — `hcore_monic`: the squarefree core is not generally monic
> (`(normalizeForFactor f).squareFreeCore` is primitive with positive
> leading coefficient via `squareFreeCore_leadingCoeff_pos_of_ne_zero`
> but the leading coefficient can exceed `1`). Removable when the
> wrapper's `Monic core` premise is relaxed to
> `Primitive + 0 < leadingCoeff` (or when an internal monicising-by-scaling
> refactor lands).

After #4879 lands, the three wrappers in
`HexBerlekampZassenhausMathlib/Basic.lean` accept
`(hcore_primitive, hcore_lc_pos)` in place of `hcore_monic`, so the
umbrella's outermost call site (line 3115 / 3316, the call to
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`)
no longer needs monicness from its boundary.

The substrate facts to discharge primitive + positive-leading
internally already exist on `main`:

* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero`
  (`HexBerlekampZassenhaus/Basic.lean:9106`).
* `IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive`
  (`HexBerlekampZassenhausMathlib/IntReductionMod.lean:646`).
* `IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive`
  (`HexBerlekampZassenhausMathlib/IntReductionMod.lean:970`).

Worker note: **the umbrella has four other internal call sites that
also pass `hcore_monic`** (lines 3063, 3072, 3079, 3084 in the aux
residual; mirrored at 3261, 3268, 3275, 3280 in the public residual):

* `factorsModP_polyProduct_congr_of_factorsModPBerlekampForm`
* `henselLiftData_liftedFactor_monic_of_choosePrimeData`
* `henselLiftData_liftedFactor_natDegree_pos_of_factorsModPBerlekampForm`
* `henselLiftData_liftedFactor_injective_of_factorsModPBerlekampForm`

These call into modular-reduction / Hensel-lift helpers that may
genuinely need monic for the leading coefficient to mod to a unit
(see #4640 deliverable 6).  In addition, the umbrella body invokes
`reassemblyExpansionComplete_exhaustive_of_ne_zero`
(`IntReductionMod.lean:3422`), which itself takes `hcore_monic` and
threads it into the `expansion_preconditions` / `_monic` /
`_degree_pos` chain.  See **Decomposition guidance** below.

depends-on: #4879

## Deliverables

In `HexBerlekampZassenhausMathlib/IntReductionMod.lean`:

1. Drop the explicit `hcore_monic` premise from
   `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData`
   (line 3573) **and** from its private aux residual
   `factor_exhaustive_branch_entry_irreducible_of_choosePrimeData_aux`
   (line 2974).

2. Derive the replacement primitive + positive-leading premises
   internally from `hf_ne : f ≠ 0`:

   ```lean
   have hcore_primitive : Hex.ZPoly.Primitive
       (Hex.normalizeForFactor f).squareFreeCore :=
     IntReductionMod.zpoly_primitive_of_toPolynomial_isPrimitive
       (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_isPrimitive f hf_ne)
   have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff
       (Hex.normalizeForFactor f).squareFreeCore :=
     Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
   ```

3. Update the internal call to
   `factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
   (the outermost wrapper call at line 3115 / 3316) to pass
   `hcore_primitive` + `hcore_lc_pos` instead of `hcore_monic`.

4. Adjust the umbrella's docstring (lines 2900-2935 region) to remove
   the Gap 1 documentation, since the gap is now closed.  Update the
   Gap inventory to reflect that only Gap 2 (`hcomplete`) and Gap 3
   (modulus / precision) remain.

5. Adjust the local `hcore_ne` derivation (lines 3003-3009 / 3209-3214)
   which currently derives `core ≠ 0` from `hcore_monic` — derive it
   from `hcore_lc_pos` instead (a polynomial with positive leading
   coefficient is nonzero).

6. **Audit the remaining four internal call sites that pass
   `hcore_monic`** (lines 3063, 3072, 3079, 3084; mirror at 3261,
   3268, 3275, 3280) into:
   * `factorsModP_polyProduct_congr_of_factorsModPBerlekampForm`
   * `henselLiftData_liftedFactor_monic_of_choosePrimeData`
   * `henselLiftData_liftedFactor_natDegree_pos_of_factorsModPBerlekampForm`
   * `henselLiftData_liftedFactor_injective_of_factorsModPBerlekampForm`

   Plus the `reassemblyExpansionComplete_exhaustive_of_ne_zero` call
   at line 3600.  Determine for each whether the downstream lemma's
   monic requirement can be relaxed (it genuinely needs primitive +
   pos-lc, or its monic premise can be discharged from the good-prime
   condition) or whether monic is essential for an unrelated reason
   (modular reduction may legitimately need it).

   For each genuinely-needing-monic downstream call, either:
   * thread a separate `hcore_monic` proof if it can be discharged
     from the new substrate, or
   * **file a separate sub-issue** tracking that helper's monic
     requirement as a residual gap and `coordination skip` this issue
     until the residual gaps are resolved (or implement only the
     achievable subset and document the residual gaps in this issue's
     PR).

No new `sorry`, `axiom`, `native_decide`, `TODO`, or `FIXME`.

## Decomposition guidance

Worker-led decomposition is encouraged (see `agent-worker-flow`).
The four internal call sites (deliverable 6) may turn out to require
their own substrate refactors before they can be relaxed.  If the
substrate work is large, file a precursor sub-issue per helper,
`coordination skip` this issue, and let the next planner cycle pick
up the umbrella drop once the substrate sub-issues land.

If the audit in deliverable 6 shows that all downstream helpers can
take `hcore_monic` synthesised from `(normalizeForFactor f).squareFreeCore`
being monic-after-scaling (via the good-prime condition) without a
refactor, the umbrella drop becomes a single-PR change.

## Library placement

* **SPEC §:** `SPEC/Libraries/hex-berlekamp-zassenhaus.md` —
  Mathlib-bridge HO-1 umbrella for the exhaustive arm.
* **Mathlib use:** yes. All work in
  `HexBerlekampZassenhausMathlib/IntReductionMod.lean` (plus any
  downstream helper relaxations that get bundled in or filed
  separately).

## Verification

* `lake build HexBerlekampZassenhausMathlib.IntReductionMod`
* `lake build HexBerlekampZassenhausMathlib`
* `lake build HexBerlekampZassenhaus`
* `python3 scripts/check_dag.py`
* `git diff --check`
* `rg -n "sorry|axiom|native_decide|TODO|FIXME" HexBerlekampZassenhausMathlib/IntReductionMod.lean`
  shows no new entries on the diff against `origin/main`.

## Out of scope

* The wrapper relaxation in `HexBerlekampZassenhausMathlib/Basic.lean`
  (covered by prerequisite #4879).
* Closing Gap 2 (`hcomplete` discharger) or Gap 3 (modulus / precision)
  in the umbrella — separate sub-issues (#4627 covered Gap 2 via
  #4865; Gap 3 remains open).
* Wiring the final `factor_irreducible_of_nonUnit` capstone (#4170).
* BHKS Theorem 5.2 / directive #2567.
* Editing `SPEC/`, top-level `PLAN.md`, or `AGENTS.md`.
