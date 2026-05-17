## Current state

`henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData` in
`HexBerlekampZassenhausMathlib/Basic.lean` (line 4327, landed in #4547)
takes an explicit `hfactors_natDegree_pos` premise:

```lean
(hfactors_natDegree_pos :
  letI := primeData.bounds
  ∀ g ∈ primeData.factorsModP,
    0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree)
```

The docstring (lines 4314-4326) records that this premise is exposed
explicitly only because discharging it from `choosePrimeData`
invariants "requires composing with `factorsModPBerlekampForm` and the
underlying Berlekamp factor-degree positivity, which lives in a
separate substrate task." This issue is that substrate task.

Both halves exist in skeletal form:

- `Hex.factorsModPBerlekampForm` (`HexBerlekampZassenhaus/Basic.lean:1580`)
  records that `data.factorsModP` is the Berlekamp factor array of
  `Hex.monicModularImage (Hex.ZPoly.modP data.p f)` together with
  primality, nonzero-image, and field witnesses.
- The Mathlib-free `berlekampFactorLoop_invariant`
  (`HexBerlekamp/Factor.lean:997`) already carries
  `∀ g ∈ ..., 0 < g.degree?.getD 0` as part of its conclusion. The
  positive-degree branch of
  `berlekampFactor_factors_nodup_of_no_squared` (lines 1041-1057) uses
  it once for the `Nodup` proof but does not export the
  positive-degree conclusion as a standalone theorem.

The sibling pattern is `factorsModP_nodup_of_factorsModPBerlekampForm`
(`HexBerlekampZassenhausMathlib/Basic.lean:4010`, landed in #4530),
which discharges the `hfactorsModP_nodup` premise on the injectivity
umbrella from `factorsModPBerlekampForm` + `isGoodPrime`. This issue
builds the parallel discharge for the natural-degree positivity
premise on the natDegree-positivity umbrella.

## Deliverables

1. **Mathlib-free side** — add
   `berlekampFactor_factors_pos_degree` to `HexBerlekamp/Factor.lean`,
   adjacent to `berlekampFactor_factors_nodup_of_no_squared` (around
   line 1031). Signature roughly:

   ```lean
   theorem berlekampFactor_factors_pos_degree
       [Lean.Grind.Field (ZMod64 p)]
       [ZMod64.PrimeModulus p]
       (f : FpPoly p) (hmonic : DensePoly.Monic f)
       (hf_pos : 0 < f.degree?.getD 0) :
       ∀ g ∈ (berlekampFactor f hmonic).factors, 0 < g.degree?.getD 0
   ```

   Proof: replay the positive-degree branch of
   `berlekampFactor_factors_nodup_of_no_squared` lines 1041-1057,
   extracting the second component of `berlekampFactorLoop_invariant`'s
   conjunction instead of the first. The squareness-free hypothesis is
   not needed for positivity (positivity is preserved by every loop
   step regardless of square-freeness), so the abstract form can be
   stated without `h_no_squared`. Keep the existing
   `berlekampFactor_factors_nodup_of_no_squared` untouched.

2. **Mathlib-bridge side** — add
   `factorsModP_natDegree_pos_of_factorsModPBerlekampForm` to
   `HexBerlekampZassenhausMathlib/Basic.lean`, adjacent to
   `factorsModP_nodup_of_factorsModPBerlekampForm` (around line 4010).
   Signature mirrors that sibling:

   ```lean
   theorem factorsModP_natDegree_pos_of_factorsModPBerlekampForm
       (f : Hex.ZPoly) (data : Hex.PrimeChoiceData)
       (hform : Hex.factorsModPBerlekampForm f data)
       (hgood :
         letI := data.bounds
         Hex.isGoodPrime f data.p = true)
       (hf_pos : 0 < f.degree?.getD 0) :
       letI := data.bounds
       ∀ g ∈ data.factorsModP,
         0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree
   ```

   Proof shape (mirroring the existing Nodup sibling):

   - Extract the `factorsModPBerlekampForm` existential to view
     `data.factorsModP.toArray` as
     `(berlekampFactor (monicModularImage (modP data.p f)) _).factors.toArray`.
   - Apply the new Mathlib-free
     `berlekampFactor_factors_pos_degree` to get
     `∀ h ∈ ..., 0 < h.degree?.getD 0`. The required positivity of the
     monic modular image follows from `0 < f.degree?.getD 0` together
     with `isGoodPrime` (which gives `(modP data.p f).isZero = false`
     and `leadingCoeff (modP data.p f) ≠ 0`, ensuring `monicModularImage`
     preserves the degree of `modP data.p f`; degree preservation from
     `f` to `modP data.p f` is the `isGoodPrime` leading-coefficient
     admissibility from `isGoodPrime_leadingCoeffAdmissible`).
   - Bridge `0 < g.degree?.getD 0` in `FpPoly p` to
     `0 < (toPolynomial (liftToZ g)).natDegree` in `Polynomial ℤ`. The
     `liftToZ` step preserves degree (existing lemma; if missing,
     prove it inline as a small helper) and `toPolynomial` of a
     positive-degree `ZPoly` has positive `natDegree` (search for
     existing bridges in `HexPolyZMathlib/Basic.lean`; the
     `toMathlibPolynomial`/`toPolynomial` natDegree bridges already
     exist for the monic case used in #4547's proof, around the
     `natDegree_map_intCast_zmod_eq_of_leadingCoeff_ne_zero` and
     `toMathlibPolynomial_modP_eq_map_intCast_zmod` lemmas).

3. **Optional unconditional umbrella** — if the
   `hfactors_natDegree_pos` premise can be cleanly dropped from
   `henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData`
   using the new bridge, add a variant
   `henselLiftData_liftedFactor_natDegree_pos_of_factorsModPBerlekampForm`
   that consumes `factorsModPBerlekampForm` + `isGoodPrime` + core
   degree positivity directly, mirroring the existing pattern of the
   `_nodup`/`_injective` family. This is optional; only do it if it
   fits within the size budget without making the issue oversized.
   Otherwise leave it for a follow-up.

## Context

- `HexBerlekamp/Factor.lean` for the Mathlib-free Berlekamp loop
  invariant (lines 997-1023) and the existing
  `berlekampFactor_factors_nodup_of_no_squared` (line 1031).
- `HexBerlekampZassenhaus/Basic.lean` for `factorsModPBerlekampForm`
  (line 1580) and `isGoodPrime_squareFreeModP` (line 738), plus the
  `isGoodPrime` leading-coefficient admissibility lemmas in the same
  file.
- `HexBerlekampZassenhausMathlib/Basic.lean:4010` for the sibling
  `factorsModP_nodup_of_factorsModPBerlekampForm` to mirror.
- `HexBerlekampZassenhausMathlib/Basic.lean:4158-4362` for the
  natDegree-positivity umbrella whose premise this issue discharges.
- `HexBerlekampZassenhausMathlib/IntReductionMod.lean` for
  `toPolynomial_isPrimitive_of_zpoly_primitive` and related bridges
  added in #4544, and for the `isGoodPrime` leading-coefficient
  bridges used by #4544 deliverable 3.
- `progress/20260517T012053Z_8aac6aa7.md` (#4547 progress) for the
  "Premise shape note" and "Current frontier" sections that record
  why the explicit premise was retained and what the natural follow-up
  was.
- This is HO-1 substrate work feeding the slow-path arm of the #4170
  capstone. No directive overlap.

## Verification

- `lake build HexBerlekamp.Factor`
- `lake build HexBerlekampMathlib.Basic`
- `lake build HexBerlekampZassenhausMathlib.Basic`
- `lake build HexBerlekampZassenhausMathlib`
- `lake build HexBerlekampZassenhaus`
- `python3 scripts/check_dag.py`
- `git diff --check`
- no new `axiom`, `native_decide`, `TODO`, `FIXME`, or theorem-level
  `sorry` introduced (tactic `sorry` is also disallowed unless
  localised to a clearly-out-of-scope analytic obligation; the
  premise discharge here is pure structural plumbing and should not
  need any).

## Out of scope

- Wiring the discharged umbrella into the actual slow-path arm of
  `factor_irreducible_of_nonUnit` (#4170); that assembly composes
  this issue's output with #4543 and #4544 plus the per-branch
  irreducibility theorems and is itself a separate sub-issue.
- BHKS fast-branch substrate (directive #2567).
- Changing executable behavior in `HexBerlekamp/`,
  `HexBerlekampZassenhaus/`, or their executable callers.
- Touching `SPEC/`, `PLAN.md`, or `.claude/CLAUDE.md`.
