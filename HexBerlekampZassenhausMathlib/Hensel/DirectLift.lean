/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Classical.Recovery
public import HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.LocalFactors
import all HexBerlekampZassenhausMathlib.LiftedFactor

public section
set_option backward.proofsInPublic true

/-!
# Facts owned by the direct Hensel lift

The executable lift is performed once.  This bundle likewise constructs its
semantic invariant once and exposes all later consumers through that value.
-/

namespace HexBerlekampZassenhausMathlib

/-- Inverse index transport for a lift whose factor count is preserved. -/
@[expose]
def modPIndexOfLiftedIndex
    (data : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = data.factorsModP.size)
    (i : LiftedFactorIndex d) : ModPFactorIndex data :=
  Fin.cast hsize i

/-- Embedding form of the inverse index transport. -/
@[expose]
def liftedIndexToModPEmbedding
    (data : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = data.factorsModP.size) :
    LiftedFactorIndex d ↪ ModPFactorIndex data where
  toFun := modPIndexOfLiftedIndex data d hsize
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : ModPFactorIndex data => x.val) hij

/-- Transport a lifted support back to the unique modular support. -/
@[expose]
def modPSubsetOfLiftedSubset
    (data : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = data.factorsModP.size)
    (S : LiftedFactorSubset d) : ModPFactorSubset data :=
  S.map (liftedIndexToModPEmbedding data d hsize)

/-- The two support transports are inverse in the lifted coordinate. -/
theorem liftedSubset_modPSubset
    (data : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = data.factorsModP.size)
    (S : LiftedFactorSubset d) :
    liftedSubsetOfModPSubset data d hsize
      (modPSubsetOfLiftedSubset data d hsize S) = S := by
  ext i
  simp only [liftedSubsetOfModPSubset, modPSubsetOfLiftedSubset,
    Finset.mem_map]
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
    have hidx :
        modPIndexToLiftedEmbedding data d hsize
            (liftedIndexToModPEmbedding data d hsize k) = k := by
      apply Fin.ext
      rfl
    rw [hidx]
    exact hk
  · intro hi
    refine ⟨modPIndexOfLiftedIndex data d hsize i, ?_, ?_⟩
    · exact ⟨i, hi, rfl⟩
    · apply Fin.ext
      rfl

/-- The two support transports are inverse in the modular coordinate. -/
theorem modPSubset_liftedSubset
    (data : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = data.factorsModP.size)
    (S : ModPFactorSubset data) :
    modPSubsetOfLiftedSubset data d hsize
      (liftedSubsetOfModPSubset data d hsize S) = S := by
  apply liftedSubsetOfModPSubset_injective data d hsize
  rw [liftedSubset_modPSubset]

/-- Semantic facts attached to the one direct-coordinate lift. -/
structure DirectLiftFacts
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData) : Prop where
  /-- The polynomial lifted in the direct coordinates is monic. -/
  targetMonic :
    Hex.DensePoly.Monic
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
  /-- The lifted factors satisfy the multifactor Hensel invariant. -/
  invariant :
    letI := data.bounds
    Hex.ZPoly.QuadraticMultifactorLiftInvariant data.p
      (Hex.precisionForCoeffBound B data.p)
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      (data.factorsModP.map Hex.FpPoly.liftToZ).toList
  /-- The initial lifted product agrees with the direct target modulo `p`. -/
  productModP :
    letI := data.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ))
      (Hex.ZPoly.monicTarget core data.p
        (Hex.precisionForCoeffBound B data.p))
      data.p
  /-- Every resulting lifted factor is monic. -/
  liftedMonic :
    ∀ i : LiftedFactorIndex (Hex.ZPoly.directLiftData core B data),
      Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.directLiftData core B data) i)
  /-- Each lifted factor reduces to its corresponding modular factor. -/
  liftedModP :
    ∀ i : ModPFactorIndex data,
      letI := data.bounds
      Hex.ZPoly.modP data.p
        (liftedFactor (Hex.ZPoly.directLiftData core B data)
          (liftedIndexOfModPIndex data
            (Hex.ZPoly.directLiftData core B data)
            (henselLiftData_liftedFactors_size_eq
              (Hex.ZPoly.monicTarget core data.p
                (Hex.precisionForCoeffBound B data.p))
              (Hex.precisionForCoeffBound B data.p) data) i)) =
        modPFactor data i
  /-- Reduction maps every selected lifted product to the same modular product. -/
  subsetProductMap :
    letI := data.bounds
    ∀ S : ModPFactorSubset data,
      let d := Hex.ZPoly.directLiftData core B data
      let hsize := henselLiftData_liftedFactors_size_eq
        (Hex.ZPoly.monicTarget core data.p
          (Hex.precisionForCoeffBound B data.p))
        (Hex.precisionForCoeffBound B data.p) data
      (HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d
          (liftedSubsetOfModPSubset data d hsize S))).map
          (Int.castRingHom (ZMod data.p)) =
        HexBerlekampMathlib.toMathlibPolynomial
          (modPFactorProduct data S)

/-- Construct the semantic bundle from the selected direct modular
factorization and validated lift precision. -/
theorem directLiftFacts
    (core : Hex.ZPoly) (B : Nat) (data : Hex.PrimeChoiceData)
    (hval : ModPFactorization core data)
    (hcore_size : 0 < core.size)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B data.p)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (data.p ^ Hex.precisionForCoeffBound B data.p)) = 1) :
    DirectLiftFacts core B data := by
  letI := data.bounds
  set k := Hex.precisionForCoeffBound B data.p with hk
  set target := Hex.ZPoly.monicTarget core data.p k with htarget
  have hp : 1 < data.p := hval.prime.one_lt
  have hpk : 1 < data.p ^ k :=
    Nat.one_lt_pow (by omega) hp
  have htarget_monic : Hex.DensePoly.Monic target := by
    rw [htarget]
    exact Hex.ZPoly.monicTarget_monic core data.p k hpk
      (by simpa [hk] using hgcd) hcore_size
  have hfactors_monic :
      ∀ g ∈ data.factorsModP, Hex.DensePoly.Monic g :=
    hval.monic
  have hproduct :
      Hex.ZPoly.congr
        (Array.polyProduct (data.factorsModP.map Hex.FpPoly.liftToZ))
        target data.p := by
    have htarget_modP :
        Hex.monicModularImage (Hex.ZPoly.modP data.p core) =
          Hex.ZPoly.modP data.p target := by
      rw [htarget]
      exact monicModularImage_modP_eq_modP_monicTarget
        core data.p k hval.prime hpk (by omega)
        (by simpa [hk] using hgcd)
    have hroundtrip :
        Hex.ZPoly.congr
          (Hex.FpPoly.liftToZ
            (Hex.monicModularImage (Hex.ZPoly.modP data.p core)))
          target data.p := by
      rw [htarget_modP]
      exact Hex.FpPoly.congr_liftToZ_modP target
    exact Hex.ZPoly.congr_trans _ _ _ data.p hval.product hroundtrip
  have hinvariant :
      Hex.ZPoly.QuadraticMultifactorLiftInvariant data.p k target
        (data.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      target k data hval.prime hp (by simpa [hk] using hprecision)
      htarget_monic hfactors_monic hproduct hval.coprime hval.ne_nil
  refine
    { targetMonic := by simpa [target, k] using htarget_monic
      invariant := by simpa [target, k] using hinvariant
      productModP := by simpa [target, k] using hproduct
      liftedMonic := ?_
      liftedModP := ?_
      subsetProductMap := ?_ }
  · intro i
    unfold liftedFactor
    simpa [Hex.ZPoly.directLiftData, target, k] using
      (henselLiftData_liftedFactor_monic target k data htarget_monic
        hinvariant hp (by simpa [hk] using hprecision) i)
  · intro i
    simpa [Hex.ZPoly.directLiftData, target, k] using
      (henselLiftData_liftedFactor_modP_eq_modPFactor
        target k data htarget_monic hinvariant hp
        (by simpa [hk] using hprecision) hfactors_monic hproduct i)
  · intro S
    dsimp only
    unfold Hex.ZPoly.directLiftData
    rw [← hk, ← htarget]
    have hcongr :=
      henselLiftData_liftedSubset_product_congr_mod_base
        target k data htarget_monic hinvariant hp
        (by simpa [hk] using hprecision) hfactors_monic hproduct S
    have hmap :=
      HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
        (liftedFactorProduct (Hex.henselLiftData target k data)
          (liftedSubsetOfModPSubset data
            (Hex.henselLiftData target k data)
            (henselLiftData_liftedFactors_size_eq target k data) S))
        (Hex.FpPoly.liftToZ (modPFactorProduct data S))
        data.p hcongr
    calc
      _ = (HexPolyZMathlib.toPolynomial
          (Hex.FpPoly.liftToZ (modPFactorProduct data S))).map
            (Int.castRingHom (ZMod data.p)) := hmap
      _ = HexBerlekampMathlib.toMathlibPolynomial
          (modPFactorProduct data S) := by
        rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod
          (Hex.FpPoly.liftToZ (modPFactorProduct data S)),
          Hex.FpPoly.modP_liftToZ]

end HexBerlekampZassenhausMathlib
