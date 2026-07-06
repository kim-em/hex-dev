/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.TrialProofs
public meta import HexBerlekampZassenhaus.TrialProofs
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.IrreducibleCore
import all HexBerlekampZassenhaus.RecombineProofs
import all HexBerlekampZassenhaus.TrialProofs

public section
set_option backward.proofsInPublic true

/-!
This module collects the quadratic-integer-root correctness proofs.
-/
namespace Hex

/-- Every factor emitted by the standalone integer trial-division core is
irreducible when `core` is a primitive, square-free polynomial with
positive leading coefficient and the bound `B` covers the coefficients of
every divisor of `core`.

Three emitted-factor families are handled uniformly:

- integer-root split factors (`split.1`), via
  `splitIntegerRootFactorsAux_factor_irreducible`;
- peeled bounded-coefficient candidates (`peel.1`), via
  `trialDivisionPeel_factor_irreducible`;
- the optional final residual (`peel.2`, when not `1`), via
  `trialDivisionPeel_residual_irreducible`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible
    (core : ZPoly) (B : Nat)
    (hcore_ne : core ≠ 0)
    (hcore_prim : ZPoly.Primitive core)
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_sq : Hex.ZPoly.SquareFreeRat core)
    (hbound : ∀ g, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B) :
    ∀ factor ∈ (exhaustiveIntegerTrialCoreFactorsWithBound core B).toList,
      ZPoly.Irreducible factor := by
  intro factor hmem
  let roots := integerRootCandidates core
  let split := splitIntegerRootFactorsAux core roots roots.length
  let candidates := trialDivisionCandidatesUpTo B (split.2.degree?.getD 0 / 2)
  let peel := trialDivisionPeelAux split.2 candidates
  have hsplit_prod : split.2 * Array.polyProduct split.1 = core :=
    splitIntegerRootFactorsAux_product core roots roots.length split.1 split.2 rfl
  have hsplit2_dvd_core : split.2 ∣ core :=
    ⟨Array.polyProduct split.1, hsplit_prod.symm⟩
  have hsplit_lc_pos :
      0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
    splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
      roots.length split.1 split.2 rfl
  have hsplit1_ne : Array.polyProduct split.1 ≠ 0 := by
    intro hz; rw [hz] at hsplit_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos; omega
  have hsplit2_ne : split.2 ≠ 0 := by
    intro hz; apply hcore_ne
    rw [← hsplit_prod, hz]; exact DensePoly.zero_mul _
  have hsplit2_pos : 0 < DensePoly.leadingCoeff split.2 := by
    have hlc :
        DensePoly.leadingCoeff core =
          DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) := by
      rw [← hsplit_prod]
      exact ZPoly.leadingCoeff_mul_of_nonzero split.2 (Array.polyProduct split.1)
        hsplit2_ne hsplit1_ne
    by_cases hp : 0 < DensePoly.leadingCoeff split.2
    · exact hp
    · exfalso
      have hle : DensePoly.leadingCoeff split.2 ≤ 0 := by omega
      have hnn : 0 ≤ DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.le_of_lt hsplit_lc_pos
      have hna : 0 ≤ -DensePoly.leadingCoeff split.2 := by omega
      have hprod_neg :
          0 ≤ -DensePoly.leadingCoeff split.2 *
            DensePoly.leadingCoeff (Array.polyProduct split.1) :=
        Int.mul_nonneg hna hnn
      have hneg_eq :
          -DensePoly.leadingCoeff split.2 *
              DensePoly.leadingCoeff (Array.polyProduct split.1) =
            -(DensePoly.leadingCoeff split.2 *
                DensePoly.leadingCoeff (Array.polyProduct split.1)) :=
        Int.neg_mul _ _
      rw [hneg_eq, ← hlc] at hprod_neg
      omega
  change factor ∈
      (if peel.2 = 1 then split.1 ++ peel.1 else (split.1 ++ peel.1).push peel.2).toList
    at hmem
  by_cases hres_one : peel.2 = 1
  · rw [if_pos hres_one] at hmem
    rw [Array.toList_append, List.mem_append] at hmem
    rcases hmem with hsplit_mem | hpeel_mem
    · exact splitIntegerRootFactorsAux_factor_irreducible
        (target := core) (roots := roots) (fuel := roots.length)
        (factors := split.1) (residual := split.2) rfl hsplit_mem
    · exact trialDivisionPeel_factor_irreducible hcore_ne hcore_prim hcore_sq
        hsplit2_dvd_core hsplit2_pos hbound rfl hpeel_mem
  · rw [if_neg hres_one] at hmem
    rw [Array.toList_push, List.mem_append] at hmem
    rcases hmem with hpref_mem | hres_mem
    · rw [Array.toList_append, List.mem_append] at hpref_mem
      rcases hpref_mem with hsplit_mem | hpeel_mem
      · exact splitIntegerRootFactorsAux_factor_irreducible
          (target := core) (roots := roots) (fuel := roots.length)
          (factors := split.1) (residual := split.2) rfl hsplit_mem
      · exact trialDivisionPeel_factor_irreducible hcore_ne hcore_prim hcore_sq
          hsplit2_dvd_core hsplit2_pos hbound rfl hpeel_mem
    · have hfactor_eq : factor = peel.2 := by
        rcases List.mem_singleton.mp hres_mem with rfl
        rfl
      rw [hfactor_eq]
      exact trialDivisionPeel_residual_irreducible hcore_ne hcore_prim hcore_sq
        hsplit2_dvd_core hsplit2_pos hbound rfl hres_one

/-- `positiveDivisors n` returns a duplicate-free list of natural divisors:
the underlying source `List.range (n + 1)` is `Nodup`, and `List.filter`
preserves this. -/
private theorem positiveDivisors_nodup (n : Nat) :
    (positiveDivisors n).Nodup := by
  unfold positiveDivisors
  exact (List.nodup_range : (List.range (n + 1)).Nodup).filter _

/-- Helper: `Nodup` of the per-divisor pair-list flat-map is preserved as
long as every divisor is positive. The positivity rules out `d = -d` and
ensures `[d, -d]` and `[d', -d']` are disjoint for distinct positive
`d ≠ d'`. -/
private theorem nodup_flatMap_pos_divisor_pairs (ds : List Nat)
    (hds_nodup : ds.Nodup) (hds_pos : ∀ d ∈ ds, 0 < d) :
    (ds.flatMap fun d => [Int.ofNat d, -Int.ofNat d]).Nodup := by
  induction ds with
  | nil => simp
  | cons d rest ih =>
      simp only [List.flatMap_cons]
      rcases List.nodup_cons.mp hds_nodup with ⟨hd_not_mem, hrest_nodup⟩
      have hd_pos : 0 < d := hds_pos d (by simp)
      have hrest_pos : ∀ d' ∈ rest, 0 < d' := by
        intro d' hd'
        exact hds_pos d' (by simp [hd'])
      have ih' := ih hrest_nodup hrest_pos
      rw [List.nodup_append]
      refine ⟨?_, ih', ?_⟩
      · -- `[Int.ofNat d, -Int.ofNat d].Nodup`
        simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil,
          List.nodup_nil, and_true, not_false_eq_true]
        intro hself
        have hd_int : (d : Int) > 0 := by exact_mod_cast hd_pos
        have : (Int.ofNat d : Int) = -(Int.ofNat d : Int) := hself
        have hcoe : (Int.ofNat d : Int) = (d : Int) := rfl
        rw [hcoe] at this
        omega
      · -- Disjointness with the rest of the flatMap
        intro a ha_pair b hb_rest hab
        rcases List.mem_flatMap.mp hb_rest with ⟨d', hd'_mem, hb_mem⟩
        have hd'_pos : 0 < d' := hrest_pos d' hd'_mem
        have hd_ne_d' : d ≠ d' := by
          intro hde
          apply hd_not_mem
          rw [hde]
          exact hd'_mem
        have hd_int : (d : Int) > 0 := by exact_mod_cast hd_pos
        have hd'_int : (d' : Int) > 0 := by exact_mod_cast hd'_pos
        have hd_int_ne : (d : Int) ≠ (d' : Int) := by
          intro h
          have : d = d' := by exact_mod_cast h
          exact hd_ne_d' this
        have hcoe : (Int.ofNat d : Int) = (d : Int) := rfl
        have hcoe' : (Int.ofNat d' : Int) = (d' : Int) := rfl
        -- Concretely unfold membership in the two-element list.
        have ha_dec : a = Int.ofNat d ∨ a = -Int.ofNat d := by
          simpa using ha_pair
        have hb_dec : b = Int.ofNat d' ∨ b = -Int.ofNat d' := by
          simpa using hb_mem
        rcases ha_dec with ha | ha <;> rcases hb_dec with hb | hb <;>
          (rw [ha, hcoe] at hab; rw [hb, hcoe'] at hab; omega)

/-- `integerRootCandidates f` returns a duplicate-free list of candidate
integer roots: positive divisors are distinct, and the per-divisor pair
`[d, -d]` is duplicate-free for `d ≠ 0` (which `positiveDivisors` ensures by
filtering out `d = 0`). The two pairs for distinct positive `d₁ ≠ d₂` share
no elements either. Consumed by the #4785 pairwise non-association proof
together with `splitIntegerRootFactorsAux_factors_form` to read off
pairwise distinctness of the factor roots. -/
private theorem integerRootCandidates_nodup (f : ZPoly) :
    (integerRootCandidates f).Nodup := by
  unfold integerRootCandidates
  apply nodup_flatMap_pos_divisor_pairs
  · exact positiveDivisors_nodup _
  · intro d hd
    unfold positiveDivisors at hd
    rw [List.mem_filter] at hd
    rcases hd with ⟨_hmem, hpred⟩
    simp at hpred
    omega

/-- **#4747 HO-1 support lemma — `normalizeFactorSign` identity on quadratic-arm
core factors.** Every factor emitted by `quadraticIntegerRootFactors? core` is a
fixed point of `normalizeFactorSign`. For linear factors `linearFactorForRoot r`,
the leading coefficient is `1`; for the optional residual, positivity of its
leading coefficient is forced by `0 < DensePoly.leadingCoeff core` combined with
the splitter invariant
`splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos`. Used by the
Mathlib-side discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` to discharge
the `hnorm` precondition of
`normalizeForFactor_repeatedPart_isFactorPower_polyProduct_of_irreducible_factors_cover`
(#4759). -/
theorem quadraticIntegerRootFactors?_normalizeFactorSign
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, normalizeFactorSign factor = factor := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hsplit_norm :
        ∀ factor ∈ split.1.toList, normalizeFactorSign factor = factor := by
      simpa [split, roots] using
        splitIntegerRootFactorsAux_normalizeFactorSign core roots roots.length
          split.1 split.2 rfl
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hsplit_norm
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          intro factor hmem
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          cases hmem with
          | inl hsplit_mem =>
              exact hsplit_norm factor hsplit_mem
          | inr hres =>
              rw [hres]
              apply normalizeFactorSign_eq_self_of_leadingCoeff_nonneg
              change 0 ≤ DensePoly.leadingCoeff split.2
              have hsplit_prod :
                  split.2 * Array.polyProduct split.1 = core := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_product core roots roots.length
                    split.1 split.2 rfl
              have hsplit_lc_pos :
                  0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots roots.length
                    split.1 split.2 rfl
              have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
                intro hzero
                rw [hzero] at hsplit_lc_pos
                rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos
                omega
              have hres_ne : split.2 ≠ 0 := by
                intro hzero
                have hcore_zero : core = 0 := by
                  rw [← hsplit_prod, hzero]
                  exact DensePoly.zero_mul _
                rw [hcore_zero] at hcore_pos
                rw [DensePoly.leadingCoeff_zero] at hcore_pos
                omega
              have hlc :
                  DensePoly.leadingCoeff core =
                    DensePoly.leadingCoeff split.2 *
                      DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                rw [← hsplit_prod]
                exact ZPoly.leadingCoeff_mul_of_nonzero
                    split.2 (Array.polyProduct split.1) hres_ne hsplit_poly_ne
              by_cases hnonneg : 0 ≤ DensePoly.leadingCoeff split.2
              · exact hnonneg
              · have hle : DensePoly.leadingCoeff split.2 < 0 := by omega
                have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                  rw [hlc]
                  exact Int.mul_neg_of_neg_of_pos hle hsplit_lc_pos
                omega
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

theorem quadraticIntegerRootFactors?_shouldRecord
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, shouldRecordPolynomialFactor factor = true := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hsplit_record :
        ∀ factor ∈ split.1.toList, shouldRecordPolynomialFactor factor = true := by
      simpa [split, roots] using
        splitIntegerRootFactorsAux_shouldRecord core roots roots.length
          split.1 split.2 rfl
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hsplit_record
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          intro factor hmem
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          cases hmem with
          | inl hsplit_mem =>
              exact hsplit_record factor hsplit_mem
          | inr hres =>
              rw [hres]
              have hsplit_prod :
                  split.2 * Array.polyProduct split.1 = core := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_product core roots roots.length
                    split.1 split.2 rfl
              have hsplit_lc_pos :
                  0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                simpa [split, roots] using
                  splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots roots.length
                    split.1 split.2 rfl
              have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
                intro hzero
                rw [hzero] at hsplit_lc_pos
                rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos
                omega
              have hres_ne : split.2 ≠ 0 := by
                intro hzero
                have hcore_zero : core = 0 := by
                  rw [← hsplit_prod, hzero]
                  exact DensePoly.zero_mul _
                rw [hcore_zero] at hcore_pos
                rw [DensePoly.leadingCoeff_zero] at hcore_pos
                omega
              have hres_ne_one : split.2 ≠ 1 := hres_one
              have hres_ne_neg_one : split.2 ≠ DensePoly.C (-1 : Int) := by
                intro hneg_one
                have hlc :
                    DensePoly.leadingCoeff core =
                      DensePoly.leadingCoeff split.2 *
                        DensePoly.leadingCoeff (Array.polyProduct split.1) := by
                  rw [← hsplit_prod]
                  exact ZPoly.leadingCoeff_mul_of_nonzero
                    split.2 (Array.polyProduct split.1) hres_ne hsplit_poly_ne
                rw [hneg_one] at hlc
                have hneg_lc :
                    DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = -1 := by simp
                rw [hneg_lc] at hlc
                have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                  rw [hlc]
                  omega
                omega
              simp [shouldRecordPolynomialFactor, split, roots, hres_ne, hres_ne_one,
                hres_ne_neg_one]
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- In the quadratic integer-root branch, every emitted factor other than the
optional final residual comes from the integer-root splitter and is therefore
irreducible. When the split is complete (`residual = 1`), this covers every
recorded quadratic-branch factor. -/
theorem quadraticIntegerRootFactors?_factor_irreducible_of_ne_residual
    {core : ZPoly} {factors : Array ZPoly} {factor : ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors)
    (hmem : factor ∈ factors.toList)
    (hnot_residual :
      factor ≠
        (splitIntegerRootFactorsAux core (integerRootCandidates core)
          (integerRootCandidates core).length).2) :
    ZPoly.Irreducible factor := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact splitIntegerRootFactorsAux_factor_irreducible
          (target := core) (roots := roots) (fuel := roots.length)
          (factors := split.1) (residual := split.2) rfl hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push] at hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          cases hmem with
          | inl hsplit_mem =>
              exact splitIntegerRootFactorsAux_factor_irreducible
                (target := core) (roots := roots) (fuel := roots.length)
                (factors := split.1) (residual := split.2) rfl hsplit_mem
          | inr hres =>
              exact absurd hres hnot_residual
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- The optional final residual of the quadratic integer-root branch is
irreducible whenever the core is primitive with positive leading coefficient.
The function's degree filter forces the residual's `degree?.getD 0` to be at
most `1`; primitivity rules out degree-`0` residuals (which would be non-unit
constants dividing every coefficient of the primitive core); hence the
residual, when emitted, has size two and is irreducible by the
`irreducible_of_size_two_primitive` companion of `_monic`, applied to the
residual's own primitivity inherited from the product `split.2 *
polyProduct split.1 = core`.

This helper exists for `_factor_irreducible_of_primitive` (the public
combined wrapper); callers outside this file should prefer the wrapper
because its signature avoids referencing the file-`private`
`splitIntegerRootFactorsAux` and `integerRootCandidates`. -/
private theorem quadraticIntegerRootFactors?_residual_irreducible
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hquad : quadraticIntegerRootFactors? core = some factors)
    {factor : ZPoly}
    (hmem : factor ∈ factors.toList)
    (hres : factor =
      (splitIntegerRootFactorsAux core (integerRootCandidates core)
        (integerRootCandidates core).length).2) :
    ZPoly.Irreducible factor := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · -- split.2 = 1: factor = 1 from hres. But hmem : factor ∈ split.1.toList,
        -- and every element of split.1 is irreducible.
        rw [if_pos hres_one] at hquad
        cases hquad
        exact splitIntegerRootFactorsAux_factor_irreducible
          (target := core) (roots := roots) (fuel := roots.length)
          (factors := split.1) (residual := split.2) rfl hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          have hsplit_prod :
              split.2 * Array.polyProduct split.1 = core := by
            simpa [split, roots] using
              splitIntegerRootFactorsAux_product core roots roots.length
                split.1 split.2 rfl
          have hsplit_lc_pos :
              0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
            simpa [split, roots] using
              splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
                roots.length split.1 split.2 rfl
          have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
            intro hzero
            rw [hzero] at hsplit_lc_pos
            rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos
            omega
          have hcore_ne : core ≠ 0 := by
            intro hzero
            rw [hzero] at hcore_pos
            rw [DensePoly.leadingCoeff_zero] at hcore_pos
            omega
          -- factor = split.2 from hres. Need: Irreducible split.2.
          rw [hres]
          have hres_ne_zero : split.2 ≠ 0 := by
            intro hzero
            apply hcore_ne
            rw [← hsplit_prod, hzero, DensePoly.zero_mul]
          have hres_size_pos : 0 < split.2.size :=
            ZPoly.size_pos_of_ne_zero split.2 hres_ne_zero
          have hres_size_le : split.2.size ≤ 2 := by
            unfold DensePoly.degree? at hres_deg
            have hnz : split.2.size ≠ 0 := by omega
            simp [hnz] at hres_deg
            omega
          have hcore_lc :
              DensePoly.leadingCoeff core =
                DensePoly.leadingCoeff split.2 *
                  DensePoly.leadingCoeff (Array.polyProduct split.1) := by
            rw [← hsplit_prod]
            exact ZPoly.leadingCoeff_mul_of_nonzero
              split.2 (Array.polyProduct split.1) hres_ne_zero hsplit_poly_ne
          -- size = 1 case: derive contradiction via primitivity.
          rcases (by omega : split.2.size = 1 ∨ split.2.size = 2) with h_one_size | h_two_size
          · exfalso
            have hres_eq : split.2 = DensePoly.C (split.2.coeff 0) :=
              ZPoly.eq_C_of_size_eq_one split.2 h_one_size
            have hcore_expand :
                core = DensePoly.C (split.2.coeff 0) * Array.polyProduct split.1 := by
              rw [← hsplit_prod]
              exact congrArg (· * Array.polyProduct split.1) hres_eq
            have hcoeff_core : ∀ n, core.coeff n =
                split.2.coeff 0 * (Array.polyProduct split.1).coeff n := by
              intro n
              rw [hcore_expand, ZPoly.C_mul_eq_scale,
                DensePoly.coeff_scale (R := Int) (split.2.coeff 0) _ n (Int.mul_zero _)]
            have hc_dvd : ∀ n, ((split.2.coeff 0).natAbs : Int) ∣ core.coeff n := by
              intro n
              rw [hcoeff_core]
              exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
            have hc_dvd_content :
                ((split.2.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
              ZPoly.dvd_content_of_nat_dvd_coeff core _ hc_dvd
            rw [show ZPoly.content core = 1 from hcore_primitive] at hc_dvd_content
            have hc_ne : split.2.coeff 0 ≠ 0 := by
              intro h
              apply hres_ne_zero
              rw [hres_eq, h]; rfl
            have hres_lc : DensePoly.leadingCoeff split.2 = split.2.coeff 0 := by
              rw [DensePoly.leadingCoeff_eq_coeff_last split.2 (by omega)]
              congr 1; omega
            rw [hres_lc] at hcore_lc
            have hc_pos : 0 < split.2.coeff 0 := by
              rcases Int.lt_or_lt_of_ne hc_ne with hlt | hgt
              · exfalso
                have : DensePoly.leadingCoeff core < 0 := by
                  rw [hcore_lc]
                  exact Int.mul_neg_of_neg_of_pos hlt hsplit_lc_pos
                omega
              · exact hgt
            have hnat_dvd : (split.2.coeff 0).natAbs ∣ (1 : Nat) :=
              Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
            have hnat_le : (split.2.coeff 0).natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
            have hnat_pos : 1 ≤ (split.2.coeff 0).natAbs := by
              rcases Nat.eq_zero_or_pos (split.2.coeff 0).natAbs with hz | hp
              · exact absurd (Int.natAbs_eq_zero.mp hz) hc_ne
              · exact hp
            have hnat_eq : (split.2.coeff 0).natAbs = 1 := by omega
            have hc_eq_one : split.2.coeff 0 = 1 := by
              rcases Int.natAbs_eq (split.2.coeff 0) with hpos | hneg
              · rw [hpos, hnat_eq]; rfl
              · exfalso
                have : split.2.coeff 0 = -1 := by rw [hneg, hnat_eq]; rfl
                omega
            apply hres_one
            rw [hres_eq, hc_eq_one]
            rfl
          · -- size = 2 case: prove irreducibility directly.
            -- We mirror irreducible_of_size_two_primitive but use core's primitivity
            -- (rather than split.2's own primitivity, which we'd otherwise need to
            -- derive from `core = split.2 * polyProduct split.1`).
            refine
              { not_zero := hres_ne_zero
                not_unit := ?_
                no_factors := ?_ }
            · intro hunit
              rcases hunit with hone | hneg_unit
              · rw [hone] at h_two_size
                have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
                omega
              · rw [hneg_unit] at h_two_size
                have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
                omega
            · intro a b hab
              by_cases ha_zero : a = 0
              · exfalso; apply hres_ne_zero
                rw [hab, ha_zero, DensePoly.zero_mul]
              by_cases hb_zero : b = 0
              · exfalso; apply hres_ne_zero
                rw [hab, hb_zero]
                change a * (0 : ZPoly) = 0
                rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
              have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
              have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
              have hab_size :
                  (a * b).size = a.size + b.size - 1 :=
                ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
              rw [← hab] at hab_size
              rw [h_two_size] at hab_size
              have hsum : a.size + b.size = 3 := by omega
              -- The constant-factor argument: if a = C c (size 1), then
              --   core = split.2 * polyProduct split.1 = a * b * polyProduct split.1
              --        = C c * (b * polyProduct split.1).
              -- c divides every coeff of core, so c.natAbs ∣ content core = 1, so c = ±1.
              have const_factor_to_unit :
                  ∀ (u v : ZPoly), u.size = 1 → split.2 = u * v →
                    ZPoly.IsUnit u := by
                intro u v hu_one hsplit_uv
                have hu_eq : u = DensePoly.C (u.coeff 0) :=
                  ZPoly.eq_C_of_size_eq_one u hu_one
                have hu_ne : u ≠ 0 := by
                  intro hzero
                  apply hres_ne_zero
                  rw [hsplit_uv, hzero, DensePoly.zero_mul]
                have huc_ne : u.coeff 0 ≠ 0 := by
                  intro hzero
                  apply hu_ne
                  rw [hu_eq, hzero]; rfl
                have hcore_eq : core =
                    DensePoly.C (u.coeff 0) * (v * Array.polyProduct split.1) := by
                  rw [← hsplit_prod, hsplit_uv]
                  rw [show u * v * Array.polyProduct split.1 =
                        DensePoly.C (u.coeff 0) * v * Array.polyProduct split.1 from
                      congrArg (· * v * Array.polyProduct split.1) hu_eq]
                  rw [DensePoly.mul_assoc_poly]
                have hu_dvd : ∀ n, ((u.coeff 0).natAbs : Int) ∣ core.coeff n := by
                  intro n
                  rw [hcore_eq, ZPoly.C_mul_eq_scale,
                    DensePoly.coeff_scale (R := Int) (u.coeff 0) _ n (Int.mul_zero _)]
                  exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
                have hu_dvd_content :
                    ((u.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
                  ZPoly.dvd_content_of_nat_dvd_coeff core _ hu_dvd
                rw [show ZPoly.content core = 1 from hcore_primitive] at hu_dvd_content
                have hnat_dvd : (u.coeff 0).natAbs ∣ (1 : Nat) :=
                  Int.ofNat_dvd.mp (by simpa using hu_dvd_content)
                have hnat_le : (u.coeff 0).natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
                have hnat_pos : 1 ≤ (u.coeff 0).natAbs := by
                  rcases Nat.eq_zero_or_pos (u.coeff 0).natAbs with hz | hp
                  · exact absurd (Int.natAbs_eq_zero.mp hz) huc_ne
                  · exact hp
                have hnat_eq : (u.coeff 0).natAbs = 1 := by omega
                rcases Int.natAbs_eq (u.coeff 0) with heq | heq
                · left; rw [hu_eq, heq, hnat_eq]; rfl
                · right; rw [hu_eq, heq, hnat_eq]; rfl
              have ha_size_eq : a.size = 1 ∨ a.size = 2 := by omega
              rcases ha_size_eq with ha_one | ha_two
              · left
                exact const_factor_to_unit a b ha_one hab
              · right
                have hb_one : b.size = 1 := by omega
                exact const_factor_to_unit b a hb_one
                  (hab.trans (DensePoly.mul_comm_poly a b))
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- Every factor emitted by the quadratic integer-root branch is irreducible
when the core is primitive with positive leading coefficient. Non-residual
factors come from the integer-root splitter (linear, hence irreducible);
the optional final residual is also irreducible because primitivity rules
out degree-`0` residuals (non-unit constants would divide every coefficient
of the primitive core) and the function's degree filter restricts residuals
to size two, where the `irreducible_of_size_two_primitive` companion of
`_monic` applies via the constant-factor argument on `core`.

This is the public wrapper used by Mathlib-side callers: its
signature avoids referencing the file-`private` `splitIntegerRootFactorsAux`
and `integerRootCandidates` (the residual is identified internally via
case analysis). -/
theorem quadraticIntegerRootFactors?_factor_irreducible_of_primitive
    {core : ZPoly} {factors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hquad : quadraticIntegerRootFactors? core = some factors)
    {factor : ZPoly}
    (hmem : factor ∈ factors.toList) :
    ZPoly.Irreducible factor := by
  by_cases hres :
      factor =
        (splitIntegerRootFactorsAux core (integerRootCandidates core)
          (integerRootCandidates core).length).2
  · exact quadraticIntegerRootFactors?_residual_irreducible
      hcore_pos hcore_primitive hquad hmem hres
  · exact quadraticIntegerRootFactors?_factor_irreducible_of_ne_residual
      hquad hmem hres

theorem quadraticIntegerRootFactors?_product
    {core : ZPoly} {factors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    Array.polyProduct factors = core := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hsplit_prod :
        split.2 * Array.polyProduct split.1 = core := by
      simpa [split, roots] using
        splitIntegerRootFactorsAux_product core roots roots.length split.1 split.2 rfl
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        simpa [hres_one, ZPoly.one_mul_zpoly] using hsplit_prod
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [polyProduct_push, DensePoly.mul_comm_poly (S := Int)]
          exact hsplit_prod
        · rw [if_neg hres_deg] at hquad
          contradiction
  · simp [hdeg] at hquad

/-- **#4747 HO-1 support lemma — public surface for the polyProduct invariant of the
quadratic integer-root branch.** Whenever `quadraticIntegerRootFactors? core`
returns `some coreFactors`, the executable `Array.polyProduct` of the recorded
factors reconstructs `core` exactly. Public wrapper of the private
`quadraticIntegerRootFactors?_product`, used by the Mathlib-side
discharger `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
(`HexBerlekampZassenhausMathlib/IntReductionMod.lean`) when feeding the
factorPower repeated-part decomposition (#4759) and the no-tail divisibility
lemma (#4807) into `Hex.reassemblyExpansionComplete`. Sibling dischargers:
constant arm `Hex.reassemblyExpansionComplete_constant_of_ne_zero` (#4585 /
PR #4598); small-mod singleton arm
`Hex.reassemblyExpansionComplete_singleton_of_irreducible` (#4597). -/
theorem polyProduct_quadraticIntegerRootFactors?_some
    {core : ZPoly} {coreFactors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some coreFactors) :
    Array.polyProduct coreFactors = core :=
  quadraticIntegerRootFactors?_product hquad

/-- **#4747 HO-1 support lemma — every factor emitted by `quadraticIntegerRootFactors?`
has dense size two.** The branch is only entered when
`core.degree?.getD 0 = 2`. Linear factors emitted by the splitter are
`linearFactorForRoot r = X - r`, which has size `2` by
`linearFactorForRoot_size_eq_two`. The optional final residual has
`degree?.getD 0 ≤ 1` by construction, so its size is `≤ 2`; the case
`size = 1` (constant residual) is incompatible with primitivity of `core`
combined with positivity of `leadingCoeff core` (the same argument used in
`quadraticIntegerRootFactors?_residual_irreducible` to rule out non-unit
constant residuals).

Used by the Mathlib-side discharger
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero` to
discharge the per-factor `0 < q.degree?.getD 0` and `0 < leadingCoeff q`
preconditions of the non-monic expansion-complete surface
`expandRepeatedPartFactorArray_residual_eq_one_of_factorPower_decomposition_of_pos_lc`. -/
theorem quadraticIntegerRootFactors?_factor_size_eq_two
    {core : ZPoly} {coreFactors : Array ZPoly}
    (hcore_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hquad : quadraticIntegerRootFactors? core = some coreFactors)
    {factor : ZPoly} (hmem : factor ∈ coreFactors.toList) :
    factor.size = 2 := by
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    obtain ⟨rs, _hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form
        (target := core) (roots := roots) (fuel := roots.length)
        (factors := split.1) (residual := split.2) rfl
    have hsplit_size :
        ∀ f ∈ split.1.toList, f.size = 2 := by
      intro f hf
      rw [hshape] at hf
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hf
      exact linearFactorForRoot_size_eq_two r
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hsplit_size factor hmem
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push] at hmem
          rcases List.mem_append.mp hmem with hsplit_mem | hres_mem
          · exact hsplit_size factor hsplit_mem
          · -- Residual case: derive size = 2 by ruling out size = 1 via primitivity.
            have hfactor_eq : factor = split.2 := by
              rcases List.mem_singleton.mp hres_mem with rfl
              rfl
            rw [hfactor_eq]
            have hsplit_prod :
                split.2 * Array.polyProduct split.1 = core := by
              simpa [split, roots] using
                splitIntegerRootFactorsAux_product core roots roots.length
                  split.1 split.2 rfl
            have hsplit_lc_pos :
                0 < DensePoly.leadingCoeff (Array.polyProduct split.1) := by
              simpa [split, roots] using
                splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
                  roots.length split.1 split.2 rfl
            have hsplit_poly_ne : Array.polyProduct split.1 ≠ 0 := by
              intro hzero
              rw [hzero] at hsplit_lc_pos
              rw [DensePoly.leadingCoeff_zero] at hsplit_lc_pos
              omega
            have hcore_ne : core ≠ 0 := by
              intro hzero
              rw [hzero] at hcore_pos
              rw [DensePoly.leadingCoeff_zero] at hcore_pos
              omega
            have hres_ne_zero : split.2 ≠ 0 := by
              intro hzero
              apply hcore_ne
              rw [← hsplit_prod, hzero, DensePoly.zero_mul]
            have hres_size_pos : 0 < split.2.size :=
              ZPoly.size_pos_of_ne_zero split.2 hres_ne_zero
            have hres_size_le : split.2.size ≤ 2 := by
              unfold DensePoly.degree? at hres_deg
              have hnz : split.2.size ≠ 0 := by omega
              simp [hnz] at hres_deg
              omega
            have hcore_lc :
                DensePoly.leadingCoeff core =
                  DensePoly.leadingCoeff split.2 *
                    DensePoly.leadingCoeff (Array.polyProduct split.1) := by
              rw [← hsplit_prod]
              exact ZPoly.leadingCoeff_mul_of_nonzero
                split.2 (Array.polyProduct split.1) hres_ne_zero hsplit_poly_ne
            rcases (by omega : split.2.size = 1 ∨ split.2.size = 2) with h_one | h_two
            · exfalso
              have hres_eq : split.2 = DensePoly.C (split.2.coeff 0) :=
                ZPoly.eq_C_of_size_eq_one split.2 h_one
              have hcore_expand :
                  core = DensePoly.C (split.2.coeff 0) * Array.polyProduct split.1 := by
                rw [← hsplit_prod]
                exact congrArg (· * Array.polyProduct split.1) hres_eq
              have hcoeff_core : ∀ n, core.coeff n =
                  split.2.coeff 0 * (Array.polyProduct split.1).coeff n := by
                intro n
                rw [hcore_expand, ZPoly.C_mul_eq_scale,
                  DensePoly.coeff_scale (R := Int) (split.2.coeff 0) _ n (Int.mul_zero _)]
              have hc_dvd : ∀ n, ((split.2.coeff 0).natAbs : Int) ∣ core.coeff n := by
                intro n
                rw [hcoeff_core]
                exact Int.natAbs_dvd.mpr ⟨_, rfl⟩
              have hc_dvd_content :
                  ((split.2.coeff 0).natAbs : Int) ∣ ZPoly.content core :=
                ZPoly.dvd_content_of_nat_dvd_coeff core _ hc_dvd
              rw [show ZPoly.content core = 1 from hcore_primitive] at hc_dvd_content
              have hc_ne : split.2.coeff 0 ≠ 0 := by
                intro h
                apply hres_ne_zero
                rw [hres_eq, h]; rfl
              have hres_lc : DensePoly.leadingCoeff split.2 = split.2.coeff 0 := by
                rw [DensePoly.leadingCoeff_eq_coeff_last split.2 (by omega)]
                congr 1; omega
              rw [hres_lc] at hcore_lc
              have hc_pos : 0 < split.2.coeff 0 := by
                rcases Int.lt_or_lt_of_ne hc_ne with hlt | hgt
                · exfalso
                  have : DensePoly.leadingCoeff core < 0 := by
                    rw [hcore_lc]
                    exact Int.mul_neg_of_neg_of_pos hlt hsplit_lc_pos
                  omega
                · exact hgt
              have hnat_dvd : (split.2.coeff 0).natAbs ∣ (1 : Nat) :=
                Int.ofNat_dvd.mp (by simpa using hc_dvd_content)
              have hnat_le : (split.2.coeff 0).natAbs ≤ 1 :=
                Nat.le_of_dvd (by omega) hnat_dvd
              have hnat_pos : 1 ≤ (split.2.coeff 0).natAbs := by
                rcases Nat.eq_zero_or_pos (split.2.coeff 0).natAbs with hz | hp
                · exact absurd (Int.natAbs_eq_zero.mp hz) hc_ne
                · exact hp
              have hnat_eq : (split.2.coeff 0).natAbs = 1 := by omega
              have hc_eq_one : split.2.coeff 0 = 1 := by
                rcases Int.natAbs_eq (split.2.coeff 0) with hpos | hneg
                · rw [hpos, hnat_eq]; rfl
                · exfalso
                  have : split.2.coeff 0 = -1 := by rw [hneg, hnat_eq]; rfl
                  omega
              apply hres_one
              rw [hres_eq, hc_eq_one]
              rfl
            · exact h_two
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

private theorem toRatPoly_linearFactorForRoot_size (r : Int) :
    (ZPoly.toRatPoly (linearFactorForRoot r)).size = 2 := by
  rw [ZPoly.size_toRatPoly]
  exact linearFactorForRoot_size_eq_two r

private theorem toRatPoly_linearFactorForRoot_ne_zero (r : Int) :
    ZPoly.toRatPoly (linearFactorForRoot r) ≠ 0 :=
  ZPoly.toRatPoly_ne_zero_of_ne_zero (linearFactorForRoot r)
    (linearFactorForRoot_ne_zero r)

private theorem toRatPoly_dvd {p q : ZPoly} (h : p ∣ q) :
    ZPoly.toRatPoly p ∣ ZPoly.toRatPoly q := by
  rcases h with ⟨k, hk⟩
  exact ⟨ZPoly.toRatPoly k, by rw [hk, ZPoly.toRatPoly_mul]⟩

/-- A polynomial that is square-free over `Rat` (in the `Hex.ZPoly.SquareFreeRat`
sense) is not divisible by `(X - r)²` for any integer root `r`.

This is consumed by the pairwise non-association proof for
`quadraticIntegerRootFactors? core` (#4785, downstream of the
`reassemblyExpansionComplete` discharger #4747): if the residual final
factor were associated to an extracted linear factor `linearFactorForRoot r`,
then `linearFactorForRoot r * linearFactorForRoot r` would divide `core`,
which this lemma rules out under squarefreeness. The `(X - r)` shape of
`linearFactorForRoot r` lets us avoid a generic
`p² ∣ f → ¬ SquareFreeRat f` lemma: we work directly with the rational
derivative product rule, the divisor argument is reduced to
`(X - r).size = 2 ≤ gcd.size` after lifting to `DensePoly Rat`. -/
private theorem linearFactor_squared_not_dvd_of_squareFreeRat
    {core : ZPoly} (hne : core ≠ 0) (hsq : Hex.ZPoly.SquareFreeRat core)
    {r : Int} :
    ¬ (linearFactorForRoot r * linearFactorForRoot r) ∣ core := by
  intro hdvd
  rcases hdvd with ⟨g, hg⟩
  -- Lift the witness equation `core = L * L * g` to `DensePoly Rat`.
  let L' := ZPoly.toRatPoly (linearFactorForRoot r)
  let g' := ZPoly.toRatPoly g
  let coreRat := ZPoly.toRatPoly core
  have hcoreRat_eq : coreRat = L' * (L' * g') := by
    show ZPoly.toRatPoly core = _
    rw [hg, ZPoly.toRatPoly_mul, ZPoly.toRatPoly_mul, DensePoly.mul_assoc_poly]
  -- Divisibilities of `coreRat` and `derivative coreRat` by `L'`.
  have hL'_dvd_L'g' : L' ∣ L' * g' := ⟨g', rfl⟩
  have hL'_dvd_coreRat : L' ∣ coreRat := by
    rw [hcoreRat_eq]; exact ⟨L' * g', rfl⟩
  have hL'_dvd_deriv : L' ∣ DensePoly.derivative coreRat := by
    rw [hcoreRat_eq, DensePoly.derivative_mul L' (L' * g')]
    apply DensePoly.dvd_add_poly
    · exact DensePoly.dvd_mul_left_poly (DensePoly.derivative L') hL'_dvd_L'g'
    · exact ⟨DensePoly.derivative (L' * g'), rfl⟩
  -- Combine into divisibility of the gcd.
  have hL'_dvd_gcd : L' ∣ DensePoly.gcd coreRat (DensePoly.derivative coreRat) :=
    DensePoly.dvd_gcd L' _ _ hL'_dvd_coreRat hL'_dvd_deriv
  -- Size argument: `L'.size = 2 ≤ gcd.size`, but squarefreeness says `gcd.size ≤ 1`.
  have hL'_size : L'.size = 2 := toRatPoly_linearFactorForRoot_size r
  have hL'_size_ne : L'.size ≠ 0 := by omega
  have hcoreRat_ne : coreRat ≠ 0 :=
    ZPoly.toRatPoly_ne_zero_of_ne_zero core hne
  have hgcd_dvd_coreRat :=
    DensePoly.gcd_dvd_left coreRat (DensePoly.derivative coreRat)
  have hgcd_ne :
      DensePoly.gcd coreRat (DensePoly.derivative coreRat) ≠ 0 := by
    intro h
    apply hcoreRat_ne
    rcases hgcd_dvd_coreRat with ⟨k, hk⟩
    rw [h, DensePoly.zero_mul] at hk
    exact hk
  have hgcd_size_ne :
      (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≠ 0 := by
    intro hsize
    apply hgcd_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega)]
    exact (DensePoly.coeff_zero n).symm
  have hsize_le :=
    ZPoly.rat_size_le_of_dvd_nonzero hL'_size_ne hgcd_size_ne hL'_dvd_gcd
  have hsq' :
      (DensePoly.gcd coreRat (DensePoly.derivative coreRat)).size ≤ 1 := hsq
  omega

/-- Distinct integer roots produce non-`ZPoly`-associated `linearFactorForRoot`
outputs. Both `linearFactorForRoot r` and `linearFactorForRoot s` are monic, so
the unit factor `u` in any `Associated` witness `LF s = LF r * u` is forced to
`C 1` (the `C (-1)` branch flips the leading coefficient). With `u = C 1`,
comparing the constant coefficient yields `-r = -s`, contradicting `r ≠ s`.
Consumed by the linear-vs-linear case of
`quadraticIntegerRootFactors?_pairwise_not_associated` (#4785). -/
private theorem linearFactorForRoot_not_associated_of_ne
    {r s : Int} (hrs : r ≠ s) :
    ¬ ZPoly.Associated (linearFactorForRoot r) (linearFactorForRoot s) := by
  rintro ⟨u, hu, heq⟩
  rcases hu with hu1 | hu_neg
  · -- `u = C 1`, so `LF s = LF r`; comparing `coeff 0` gives `-s = -r`.
    have h_eq : linearFactorForRoot s = linearFactorForRoot r := by
      rw [heq, hu1]
      change linearFactorForRoot r * (1 : ZPoly) = linearFactorForRoot r
      exact DensePoly.mul_one_right_poly (S := Int) _
    have hs_coeff : (linearFactorForRoot s).coeff 0 = -s := by
      unfold linearFactorForRoot
      rw [DensePoly.coeff_ofCoeffs]
      rfl
    have hr_coeff : (linearFactorForRoot r).coeff 0 = -r := by
      unfold linearFactorForRoot
      rw [DensePoly.coeff_ofCoeffs]
      rfl
    have hcoeff_eq : (linearFactorForRoot s).coeff 0 =
        (linearFactorForRoot r).coeff 0 := by rw [h_eq]
    rw [hs_coeff, hr_coeff] at hcoeff_eq
    omega
  · -- `u = C (-1)`, so leading coefficient becomes `1 * (-1) = -1 ≠ 1`.
    have hLFr_ne : linearFactorForRoot r ≠ 0 := linearFactorForRoot_ne_zero r
    have hCneg_ne : DensePoly.C (-1 : Int) ≠ (0 : ZPoly) := by
      intro hz
      have hsize : (DensePoly.C (-1 : Int)).size = 1 := rfl
      rw [hz] at hsize
      change (0 : ZPoly).size = 1 at hsize
      have h0 : (0 : ZPoly).size = 0 := rfl
      omega
    have hlc_eq :
        DensePoly.leadingCoeff (linearFactorForRoot s) =
          DensePoly.leadingCoeff (linearFactorForRoot r) *
            DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) := by
      rw [heq, hu_neg]
      exact ZPoly.leadingCoeff_mul_of_nonzero _ _ hLFr_ne hCneg_ne
    have hC_lc : DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = (-1 : Int) := by
      simp [DensePoly.leadingCoeff,
        DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
    rw [leadingCoeff_linearFactorForRoot, leadingCoeff_linearFactorForRoot,
        hC_lc] at hlc_eq
    omega

/-- If `r ∈ rs`, then `linearFactorForRoot r` divides the left-fold product
of `rs.map linearFactorForRoot`. Proven by induction on `rs`: the head case is
direct, and the tail case lifts the inductive divisor over a single left
multiplication using `list_foldl_mul_eq_mul_foldl_one`. Consumed by the
linear-vs-residual case of
`quadraticIntegerRootFactors?_pairwise_not_associated` (#4785) to extract
a copy of `linearFactorForRoot r` from `Array.polyProduct split.1` and pair
it with the residual to yield `(linearFactorForRoot r)^2 ∣ core`, then refuted
via `linearFactor_squared_not_dvd_of_squareFreeRat`. -/
private theorem linearFactor_dvd_listFoldl_of_mem
    {rs : List Int} {r : Int} (hmem : r ∈ rs) :
    linearFactorForRoot r ∣
      (rs.map linearFactorForRoot).foldl (· * ·) (1 : ZPoly) := by
  induction rs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons head tail ih =>
    rw [List.map_cons, List.foldl_cons, ZPoly.one_mul_zpoly,
        ZPoly.list_foldl_mul_eq_mul_foldl_one (linearFactorForRoot head)
          (tail.map linearFactorForRoot)]
    rcases List.mem_cons.mp hmem with rfl | hin
    · exact ⟨(tail.map linearFactorForRoot).foldl (· * ·) 1, rfl⟩
    · obtain ⟨k, hk⟩ := ih hin
      refine ⟨linearFactorForRoot head * k, ?_⟩
      rw [hk,
          ← DensePoly.mul_assoc_poly (S := Int) (linearFactorForRoot head)
            (linearFactorForRoot r) k,
          DensePoly.mul_comm_poly (S := Int) (linearFactorForRoot head)
            (linearFactorForRoot r),
          DensePoly.mul_assoc_poly (S := Int) (linearFactorForRoot r)
            (linearFactorForRoot head) k]

/-- **#4785 HO-1 support lemma — pairwise non-association of the quadratic
integer-root branch output.** The factors emitted by
`quadraticIntegerRootFactors? core` are pairwise non-`ZPoly`-associated
whenever `core` is primitive, has positive leading coefficient, and is
square-free over `Rat[x]`.

Linear-vs-linear pairs follow from `splitIntegerRootFactorsAux_factors_form`
(the splitter records `linearFactorForRoot rᵢ` for distinct roots `rᵢ`
forming a `Sublist` of `integerRootCandidates core`, which is `Nodup`) and
`linearFactorForRoot_not_associated_of_ne`.

Linear-vs-residual pairs are ruled out by case analysis on the
`ZPoly.Associated` unit factor `u`: the `u = C (-1)` branch contradicts the
residual's positive leading coefficient (inherited from `core`'s positive
leading coefficient via the splitter's monic-product invariant), and the
`u = C 1` branch produces `(linearFactorForRoot r)^2 ∣ core`, refuted by
`linearFactor_squared_not_dvd_of_squareFreeRat`.

Combines with `irreducible_not_dvd_of_not_associated` (HO-1 support lemma #4603)
into the `reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`
discharger (#4747 residual). -/
theorem quadraticIntegerRootFactors?_pairwise_not_associated
    {core : ZPoly} (hcore_lc_pos : 0 < DensePoly.leadingCoeff core)
    (hcore_primitive : ZPoly.Primitive core)
    (hcore_squarefree : Hex.ZPoly.SquareFreeRat core)
    {coreFactors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some coreFactors) :
    coreFactors.toList.Pairwise (fun q₁ q₂ => ¬ ZPoly.Associated q₁ q₂) := by
  have hcore_ne : core ≠ 0 := by
    intro hz
    rw [hz] at hcore_lc_pos
    rw [DensePoly.leadingCoeff_zero] at hcore_lc_pos
    omega
  -- Acknowledge the primitivity hypothesis (kept in the signature for
  -- symmetry with the `_factor_irreducible_of_primitive` wrapper; the
  -- residual-leading-coefficient argument and the squared-divisibility
  -- contradiction discharge the linear-vs-residual case without it).
  have _ := hcore_primitive
  unfold quadraticIntegerRootFactors? at hquad
  by_cases hdeg : core.degree?.getD 0 = 2
  · simp only [hdeg, if_true] at hquad
    let roots := integerRootCandidates core
    let split := splitIntegerRootFactorsAux core roots roots.length
    have hroots_nodup : roots.Nodup := integerRootCandidates_nodup core
    obtain ⟨rs, hsub, hshape⟩ :=
      splitIntegerRootFactorsAux_factors_form (target := core) (roots := roots)
        (fuel := roots.length) (factors := split.1) (residual := split.2) rfl
    have hrs_nodup : rs.Nodup := hsub.nodup hroots_nodup
    -- Pairwise non-association on the splitter's recorded linears.
    have hLL :
        (split.1.toList).Pairwise (fun q₁ q₂ => ¬ ZPoly.Associated q₁ q₂) := by
      rw [hshape, List.pairwise_map]
      exact hrs_nodup.imp (fun hne => linearFactorForRoot_not_associated_of_ne hne)
    by_cases hsize : split.1.size = 0
    · simp [roots, split, hsize] at hquad
    · simp only [roots, split, hsize, if_false] at hquad
      by_cases hres_one : split.2 = 1
      · rw [if_pos hres_one] at hquad
        cases hquad
        exact hLL
      · rw [if_neg hres_one] at hquad
        by_cases hres_deg : split.2.degree?.getD 0 ≤ 1
        · rw [if_pos hres_deg] at hquad
          cases hquad
          rw [Array.toList_push]
          -- Residual leading-coefficient invariants.
          have hsplit_prod :
              split.2 * Array.polyProduct split.1 = core :=
            splitIntegerRootFactorsAux_product core roots roots.length
              split.1 split.2 rfl
          have hpoly_lc_pos :
              0 < DensePoly.leadingCoeff (Array.polyProduct split.1) :=
            splitIntegerRootFactorsAux_polyProduct_leadingCoeff_pos core roots
              roots.length split.1 split.2 rfl
          have hpoly_ne : Array.polyProduct split.1 ≠ 0 := by
            intro hz
            rw [hz] at hpoly_lc_pos
            rw [DensePoly.leadingCoeff_zero] at hpoly_lc_pos
            omega
          have hres_ne : split.2 ≠ 0 := by
            intro hz
            apply hcore_ne
            rw [← hsplit_prod, hz, DensePoly.zero_mul]
          have hcore_lc_eq :
              DensePoly.leadingCoeff core =
                DensePoly.leadingCoeff split.2 *
                  DensePoly.leadingCoeff (Array.polyProduct split.1) := by
            rw [← hsplit_prod]
            exact ZPoly.leadingCoeff_mul_of_nonzero split.2 _ hres_ne hpoly_ne
          have hres_lc_pos : 0 < DensePoly.leadingCoeff split.2 := by
            have hres_lc_ne :
                DensePoly.leadingCoeff split.2 ≠ 0 :=
              ZPoly.leadingCoeff_ne_zero_of_ne_zero split.2 hres_ne
            rcases Int.lt_or_lt_of_ne hres_lc_ne with hlt | hgt
            · exfalso
              have hcore_neg : DensePoly.leadingCoeff core < 0 := by
                rw [hcore_lc_eq]
                exact Int.mul_neg_of_neg_of_pos hlt hpoly_lc_pos
              omega
            · exact hgt
          -- Translate `Array.polyProduct split.1` to the list left-fold form.
          have hpolyProd_eq :
              Array.polyProduct split.1 =
                (rs.map linearFactorForRoot).foldl (· * ·) (1 : ZPoly) := by
            unfold Array.polyProduct
            rw [← Array.foldl_toList, hshape]
          have hcross :
              ∀ a ∈ split.1.toList, ¬ ZPoly.Associated a split.2 := by
            rw [hshape]
            intro a ha
            obtain ⟨r, hr_rs, rfl⟩ := List.mem_map.mp ha
            rintro ⟨u, hu, heq⟩
            rcases hu with hu1 | hu_neg
            · -- `u = C 1`: `split.2 = LF r`, so `(LF r)^2 ∣ core`.
              have hsplit2_eq : split.2 = linearFactorForRoot r := by
                rw [heq, hu1]
                change linearFactorForRoot r * (1 : ZPoly) = linearFactorForRoot r
                exact DensePoly.mul_one_right_poly (S := Int) _
              have hLF_dvd :
                  linearFactorForRoot r ∣ Array.polyProduct split.1 := by
                rw [hpolyProd_eq]
                exact linearFactor_dvd_listFoldl_of_mem hr_rs
              obtain ⟨k, hk⟩ := hLF_dvd
              have hdvd :
                  linearFactorForRoot r * linearFactorForRoot r ∣ core := by
                refine ⟨k, ?_⟩
                rw [← hsplit_prod, hsplit2_eq, hk,
                    DensePoly.mul_assoc_poly (S := Int)]
              exact linearFactor_squared_not_dvd_of_squareFreeRat
                hcore_ne hcore_squarefree hdvd
            · -- `u = C (-1)`: leading coefficient of `split.2` becomes `-1`.
              have hCneg_ne : DensePoly.C (-1 : Int) ≠ (0 : ZPoly) := by
                intro hz
                have hsize : (DensePoly.C (-1 : Int)).size = 1 := rfl
                rw [hz] at hsize
                change (0 : ZPoly).size = 1 at hsize
                have h0 : (0 : ZPoly).size = 0 := rfl
                omega
              have hC_lc :
                  DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) = (-1 : Int) := by
                simp [DensePoly.leadingCoeff,
                  DensePoly.coeffs_C_of_ne_zero (by decide : (-1 : Int) ≠ 0)]
              have hlc_eq :
                  DensePoly.leadingCoeff split.2 =
                    DensePoly.leadingCoeff (linearFactorForRoot r) *
                      DensePoly.leadingCoeff (DensePoly.C (-1 : Int)) := by
                rw [heq, hu_neg]
                exact ZPoly.leadingCoeff_mul_of_nonzero _ _
                  (linearFactorForRoot_ne_zero r) hCneg_ne
              rw [leadingCoeff_linearFactorForRoot, hC_lc] at hlc_eq
              rw [hlc_eq] at hres_lc_pos
              omega
          rw [List.pairwise_append]
          refine ⟨hLL, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          rw [hb]
          exact hcross a ha
        · simp [roots, split, hres_deg] at hquad
  · simp [hdeg] at hquad

/-- Every factor emitted by `quadraticIntegerRootFactors?` has positive leading
coefficient when the input core has positive leading coefficient. This packages
the normalization and recording invariants for Mathlib-side callers of the
non-monic repeated-part expansion helper. -/
theorem quadraticIntegerRootFactors?_leadingCoeff_pos
    {core : ZPoly} (hcore_pos : 0 < DensePoly.leadingCoeff core)
    {factors : Array ZPoly}
    (hquad : quadraticIntegerRootFactors? core = some factors) :
    ∀ factor ∈ factors.toList, 0 < DensePoly.leadingCoeff factor := by
  intro factor hmem
  have hnorm :
      normalizeFactorSign factor = factor :=
    quadraticIntegerRootFactors?_normalizeFactorSign hcore_pos hquad factor hmem
  have hnonneg : 0 ≤ DensePoly.leadingCoeff factor := by
    rw [← hnorm]
    exact normalizeFactorSign_leadingCoeff_nonneg factor
  have hrecord :
      shouldRecordPolynomialFactor factor = true :=
    quadraticIntegerRootFactors?_shouldRecord hcore_pos hquad factor hmem
  have hfactor_ne : factor ≠ 0 := by
    intro hzero
    unfold shouldRecordPolynomialFactor at hrecord
    simp [hzero] at hrecord
  have hlc_ne :
      DensePoly.leadingCoeff factor ≠ 0 :=
    ZPoly.leadingCoeff_ne_zero_of_ne_zero factor hfactor_ne
  omega

end Hex
