import HexBerlekampZassenhausMathlib.Basic
import HexBerlekampZassenhausMathlib.Lattice

/-!
Bridge from recovery-side lifted-factor subsets to BHKS true-factor packages.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

namespace BHKS

/--
Transport a recovery-side lifted-factor subset to the BHKS support type.

This relies on the executable `bhksLatticeBasis` computing `factorCount`
definitionally as `d.liftedFactors.size`, so the two `Fin` index types coincide.
-/
def supportOfSubset (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d) :
    LiftedFactorSupport (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors) :=
  (T : Set (LiftedFactorIndex d))

@[simp] theorem mem_supportOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d)
    (i : Fin (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors).factorCount) :
    i ∈ supportOfSubset f d T ↔ i ∈ T := by
  rfl

private theorem finRange_filter_set_perm
    {n : Nat} (T : Finset (Fin n)) :
    ((List.finRange n).filter
      (fun i => @decide (i ∈ (T : Set (Fin n)))
        (Classical.propDecidable _))).Perm T.toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.nodup_finRange n).filter _
  · exact T.nodup_toList
  · ext i
    simp [List.toFinset_filter, List.toFinset_finRange, Finset.toList_toFinset]

/-- The BHKS support product agrees with the recovery-side selected product. -/
theorem supportProduct_supportOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d) :
    supportProduct (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
        (supportOfSubset f d T) =
      liftedFactorProduct d T := by
  classical
  apply HexPolyZMathlib.equiv.injective
  simp only [HexPolyZMathlib.equiv_apply]
  unfold supportProduct supportOfSubset
  simp only [Hex.bhksLatticeBasis]
  rw [polyProduct_toPolynomial, toPolynomial_liftedFactorProduct]
  simp only [List.map_map, Function.comp_def, liftedFactor]
  trans ∏ i ∈ T, HexPolyZMathlib.toPolynomial (d.liftedFactors.getD i.val 1)
  ·
    rw [← Finset.prod_map_toList T
      (fun i => HexPolyZMathlib.toPolynomial (d.liftedFactors.getD i.val 1))]
    exact List.Perm.prod_eq (List.Perm.map _
      (finRange_filter_set_perm T))
  · refine Finset.prod_congr rfl ?_
    intro i _hi
    simp

/--
Build a BHKS true-factor package from concrete lift data plus a recovery-side
subset product witness.  The caller supplies the named `factor` because
recovery-side evidence is usually stated against an externally represented
integer factor, not just the raw selected lifted product.
-/
def trueFactorLiftOfSubset
    (f : Hex.ZPoly) (d : Hex.LiftData) (T : LiftedFactorSubset d)
    (factor cofactor : Hex.ZPoly)
    (hfactor : factor * cofactor = f)
    (hproduct : liftedFactorProduct d T = factor) :
    TrueFactorLift (Hex.bhksLatticeBasis f d.p d.k d.liftedFactors)
      (supportOfSubset f d T) where
  f := f
  p := d.p
  a := d.k
  liftedFactors := d.liftedFactors
  basis_eq := rfl
  factor := factor
  cofactor := cofactor
  factor_mul := hfactor
  support_product_eq := by
    rw [supportProduct_supportOfSubset, hproduct]

end BHKS

end

end HexBerlekampZassenhausMathlib
