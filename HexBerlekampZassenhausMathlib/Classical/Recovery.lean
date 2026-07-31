/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Modular.PrimePlan
public import HexBerlekampZassenhausMathlib.ForwardHenselTransport
public import HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.LiftedFactor

public section
set_option backward.proofsInPublic true

/-!
# Direct-coordinate recovery

This module is the single bridge from the executable direct candidate to the
proof-side M1 candidate.  It contains no dilation or `toMonic` recovery path.
-/

namespace HexBerlekampZassenhausMathlib

/-- The executable selected-list candidate is exactly the proof-side direct
candidate on the corresponding lifted subset. -/
theorem directCandidate_selected_eq
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.directCandidate (Hex.DensePoly.leadingCoeff core) (d.p ^ d.k)
        (liftedSubsetSelectedList d S) =
      scaledRecombinationCandidate core d S := by
  unfold Hex.directCandidate scaledRecombinationCandidate
    scaledLiftedFactorProduct
  rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]

/-- An indexed support list with no duplicate indices has the proof-side
finite-set product, independently of its traversal order. -/
theorem polyProduct_directSelectedFactors
    (d : Hex.LiftData) (selected : List (Hex.DirectLiftedIndex d))
    (hnodup : selected.Nodup) :
    Array.polyProduct (Hex.directSelectedFactors d selected).toArray =
      liftedFactorProduct d selected.toFinset := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [polyProduct_toPolynomial, toPolynomial_liftedFactorProduct]
  rw [List.toList_toArray]
  unfold Hex.directSelectedFactors
  rw [List.map_map]
  change
    (selected.map (fun i =>
        HexPolyZMathlib.toPolynomial (Hex.directLiftedFactor d i))).prod =
      ∏ i ∈ selected.toFinset,
        HexPolyZMathlib.toPolynomial (liftedFactor d i)
  rw [List.prod_toFinset
    (fun i : Hex.DirectLiftedIndex d =>
      HexPolyZMathlib.toPolynomial (liftedFactor d i)) hnodup]
  rfl

/-- The indexed executable candidate agrees with the proof-side candidate on
the finite support represented by the list. -/
theorem directCandidate_indexed_eq
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (selected : List (Hex.DirectLiftedIndex d))
    (hnodup : selected.Nodup) :
    Hex.directCandidate (Hex.DensePoly.leadingCoeff core) (d.p ^ d.k)
        (Hex.directSelectedFactors d selected) =
      scaledRecombinationCandidate core d selected.toFinset := by
  unfold Hex.directCandidate scaledRecombinationCandidate
    scaledLiftedFactorProduct
  rw [polyProduct_directSelectedFactors d selected hnodup]

/-- A nonzero integer whose residue modulo a prime is nonzero is coprime to
every positive power of that prime. -/
theorem gcd_primePow_eq_one_of_cast_ne_zero
    (a : Int) (p k : Nat) (hp : _root_.Nat.Prime p)
    (ha : (a : ZMod p) ≠ 0) :
    Int.gcd a (Int.ofNat (p ^ k)) = 1 := by
  rw [Int.gcd_eq_natAbs]
  change a.natAbs.gcd (p ^ k) = 1
  have hnot : ¬p ∣ a.natAbs := by
    intro hpa
    have hpInt : (p : Int) ∣ a := by
      obtain ⟨c, hc⟩ := hpa
      refine ⟨Int.sign a * c, ?_⟩
      calc
        a = Int.sign a * (a.natAbs : Int) :=
          (Int.sign_mul_natAbs a).symm
        _ = Int.sign a * ((p * c : Nat) : Int) := by rw [hc]
        _ = (p : Int) * (Int.sign a * c) := by push_cast; ring
    exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).2 hpInt)
  have hcop : a.natAbs.Coprime p :=
    Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).2 hnot)
  exact (hcop.pow_right k).gcd_eq_one

/-- Coprimality with a modulus descends along divisibility of integer leading
coefficients. -/
theorem gcd_eq_one_of_dvd_left
    {a b m : Int} (hab : a ∣ b) (hb : Int.gcd b m = 1) :
    Int.gcd a m = 1 := by
  rw [Int.gcd_eq_one_iff] at hb ⊢
  intro c hca hcm
  exact hb c (hca.trans hab) hcm

/-- The exact proportionality certificate behind direct recovery.

For an integer factor represented by a modular support, the core-scaled
product of the corresponding canonical Hensel factors is congruent to the
factor scaled by the leading coefficient of its cofactor.  CLD consumes this
statement directly; classical recovery additionally centers and
primitivizes it. -/
theorem directScaledProduct_congr_of_modP_support
    {core factor cofactor : Hex.ZPoly} {B : Nat}
    {data : Hex.PrimeChoiceData} {S : ModPFactorSubset data}
    (hval : ModPFactorization core data)
    (hcore_size : 0 < core.size)
    (hfactor_size : 0 < factor.size)
    (hproduct : factor * cofactor = core)
    (hcore_lc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff factor *
          Hex.DensePoly.leadingCoeff cofactor)
    (hgcd_core : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hgcd_factor : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hgcd_cofactor : Int.gcd (Hex.DensePoly.leadingCoeff cofactor)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hprecision_pos : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hrep : RepresentsIntegerFactorModP data factor S) :
    let d := Hex.ZPoly.coreLiftData core B data
    let T := liftedSubsetOfModPSubset data d
      (henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p))
        (Hex.precisionForCoeffBound B data.p) data) S
    Hex.ZPoly.congr
      (scaledLiftedFactorProduct core d T)
      (Hex.DensePoly.scale
        (Hex.DensePoly.leadingCoeff cofactor) factor)
      (d.p ^ d.k) := by
  letI := data.bounds
  let k := Hex.precisionForCoeffBound B data.p
  let d := Hex.ZPoly.coreLiftData core B data
  let T : LiftedFactorSubset d :=
    liftedSubsetOfModPSubset data d
      (henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p k) k data) S
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hpk : 1 < data.p ^ k :=
    Nat.one_lt_pow hk.ne' hval.prime.one_lt
  have hfactor_product :
      Hex.ZPoly.congr
        (Hex.ZPoly.monicTarget factor data.p k *
          Hex.ZPoly.monicTarget cofactor data.p k)
        (Hex.ZPoly.monicTarget core data.p k)
        (data.p ^ k) :=
    monicTarget_mul_congr hpk hproduct hcore_lc
      hgcd_core hgcd_factor hgcd_cofactor
  have hrepTarget :
      RepresentsIntegerFactorModP data
        (Hex.ZPoly.monicTarget factor data.p k) S :=
    representsMonicTarget_of_represents hval.prime hpk
      hk hfactor_size hgcd_factor hrep
  have hsubset :
      Hex.ZPoly.congr (liftedFactorProduct d T)
        (Hex.ZPoly.monicTarget factor data.p k) (data.p ^ k) := by
    simpa [d, T, k, Hex.ZPoly.coreLiftData] using
      (coreLiftData_subset_congr_monicTarget core factor B data hval
        hcore_size hprecision_pos hgcd_core hfactor_size hgcd_factor
        hfactor_product hrepTarget)
  unfold scaledLiftedFactorProduct
  exact
    (honestCongr_of_product_congr_monicTarget
      (core := core) (factor := factor) (d := d) (S := T)
      (Hex.DensePoly.leadingCoeff cofactor) hcore_lc hsubset
      hgcd_factor hpk)

/-- Direct M1 recovery from one modular support.

The Hensel subset is lifted against `monicTarget core`; Hensel uniqueness
identifies it with `monicTarget factor`.  Scaling by `lc(core)` then recovers
`lc(cofactor) • factor`, and primitive/sign normalization removes precisely
that positive scalar. -/
theorem directCandidate_eq_of_modP_support
    {core factor cofactor : Hex.ZPoly} {B : Nat}
    {data : Hex.PrimeChoiceData} {S : ModPFactorSubset data}
    (hval : ModPFactorization core data)
    (hcore_size : 0 < core.size)
    (hfactor_size : 0 < factor.size)
    (hproduct : factor * cofactor = core)
    (hcore_lc :
      Hex.DensePoly.leadingCoeff core =
        Hex.DensePoly.leadingCoeff factor *
          Hex.DensePoly.leadingCoeff cofactor)
    (hgcd_core : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hgcd_factor : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hgcd_cofactor : Int.gcd (Hex.DensePoly.leadingCoeff cofactor)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1)
    (hcofactor_lc_pos : 0 < Hex.DensePoly.leadingCoeff cofactor)
    (hfactor_prim : Hex.ZPoly.primitivePart factor = factor)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hprecision_pos : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core <
        data.p ^ Hex.precisionForCoeffBound B data.p)
    (hrep : RepresentsIntegerFactorModP data factor S) :
    let d := Hex.ZPoly.coreLiftData core B data
    scaledRecombinationCandidate core d
      (liftedSubsetOfModPSubset data d
        (henselLiftData_liftedFactors_size_eq
          (Hex.ZPoly.monicTarget core data.p
            (Hex.precisionForCoeffBound B data.p))
          (Hex.precisionForCoeffBound B data.p) data) S) = factor := by
  letI := data.bounds
  let k := Hex.precisionForCoeffBound B data.p
  let d := Hex.ZPoly.coreLiftData core B data
  let T : LiftedFactorSubset d :=
    liftedSubsetOfModPSubset data d
      (henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p k) k data) S
  have hp2 : 2 ≤ data.p := hval.prime.two_le
  have hk : 0 < k := by
    dsimp [k]
    omega
  have hpk : 1 < data.p ^ k := by
    exact Nat.one_lt_pow hk.ne' hval.prime.one_lt
  have hhonest :
      Hex.ZPoly.congr
        (scaledLiftedFactorProduct core d T)
        (Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff cofactor) factor)
        (d.p ^ d.k) := by
    simpa [d, T, k, Hex.ZPoly.coreLiftData] using
      (directScaledProduct_congr_of_modP_support
        (core := core) (factor := factor) (cofactor := cofactor)
        (B := B) (data := data) (S := S)
        hval hcore_size hfactor_size hproduct hcore_lc
        hgcd_core hgcd_factor hgcd_cofactor hprecision_pos hrep)
  exact scaledRecombinationCandidate_eq_of_factorization
    (core := core) (factor := factor) (cofactor := cofactor)
    (d := d) (S := T)
    (by
      intro hzero
      rw [hzero] at hcore_size
      simp at hcore_size)
    hproduct hcofactor_lc_pos hhonest hfactor_prim hfactor_norm
    (by simpa [d, k, Hex.ZPoly.coreLiftData] using hprecision)

end HexBerlekampZassenhausMathlib
