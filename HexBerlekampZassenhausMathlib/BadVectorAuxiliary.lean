import HexBerlekampZassenhausMathlib.BadVector

/-!
Coefficient-facing helper lemmas for the BHKS auxiliary polynomial.

These package the executable `List.range`/`DensePoly.ofCoeffs` shape used by
`BHKS.auxiliaryPolynomialWithCorrections` so downstream norm-bound proofs can
rewrite by a named coefficient formula instead of unfolding the construction.
-/

namespace HexBerlekampZassenhausMathlib

namespace BHKS

/-- Read back a mapped `List.range` coefficient list with the usual zero
default outside the range. -/
theorem list_range_getElem?_map_getD_zero {α : Type*} [Zero α]
    (size n : Nat) (f : Nat → α) :
    (Option.map f ((List.range size)[n]?)).getD (0 : α) =
      if n < size then f n else 0 := by
  by_cases hn : n < size
  · simp [hn]
  · simp [hn]

/-- Exact coefficient expansion for the corrected BHKS auxiliary polynomial. -/
theorem coeff_auxiliaryPolynomialWithCorrections
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int) (j : Nat) :
    (BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections).coeff j =
      if j < input.degree?.getD 0 then
        (List.range liftData.liftedFactors.size).foldl
          (fun acc i =>
            acc +
              vec.getD i 0 *
                (Hex.cldCoeffs input liftData.p liftData.k
                  (liftData.liftedFactors.getD i 0)).getD j 0) 0 -
          corrections.getD j 0 *
            Int.ofNat
              (liftData.p ^
                (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j))
      else 0 := by
  unfold BHKS.auxiliaryPolynomialWithCorrections
  rw [Hex.DensePoly.coeff_ofCoeffs_list]
  simpa using
    (list_range_getElem?_map_getD_zero (α := Int)
      (input.degree?.getD 0) j
      (fun j =>
        ((List.range liftData.liftedFactors.size).foldl
          (fun acc i =>
            acc +
              vec.getD i 0 *
                (Hex.cldCoeffs input liftData.p liftData.k
                  (liftData.liftedFactors.getD i 0)).getD j 0) 0 -
          corrections.getD j 0 *
            Int.ofNat
              (liftData.p ^
                (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j)))))

/-- Exact coefficient expansion for the zero-correction compatibility wrapper. -/
theorem coeff_auxiliaryPolynomial
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) (j : Nat) :
    (BHKS.auxiliaryPolynomial input liftData vec).coeff j =
      if j < input.degree?.getD 0 then
        (List.range liftData.liftedFactors.size).foldl
          (fun acc i =>
            acc +
              vec.getD i 0 *
                (Hex.cldCoeffs input liftData.p liftData.k
                  (liftData.liftedFactors.getD i 0)).getD j 0) 0
      else 0 := by
  rw [BHKS.auxiliaryPolynomial, coeff_auxiliaryPolynomialWithCorrections]
  by_cases hj : j < input.degree?.getD 0
  · simp [hj]
  · simp [hj]

/--
Sanity check for true-factor indicator rows: if the CLD block of a projected
indicator vector is exactly accounted for by the diagonal correction rows, the
corrected auxiliary polynomial is zero.

This is the abstract coefficient-level form consumed by later BHKS work; those
callers are responsible for proving the `hcoeff` hypothesis from CLD additivity
and the executable cut semantics.
-/
theorem auxiliaryPolynomialWithCorrections_eq_zero_of_coeff_correction
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int)
    (hcoeff :
      ∀ j, j < input.degree?.getD 0 →
        (List.range liftData.liftedFactors.size).foldl
          (fun acc i =>
            acc +
              vec.getD i 0 *
                (Hex.cldCoeffs input liftData.p liftData.k
                  (liftData.liftedFactors.getD i 0)).getD j 0) 0 =
          corrections.getD j 0 *
            Int.ofNat
              (liftData.p ^
                (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j))) :
    BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections = 0 := by
  apply Hex.DensePoly.ext_coeff
  intro j
  rw [coeff_auxiliaryPolynomialWithCorrections, Hex.DensePoly.coeff_zero]
  by_cases hj : j < input.degree?.getD 0
  · simp [hj]
    simpa using sub_eq_zero.mpr (hcoeff j hj)
  · simp [hj]

end BHKS

end HexBerlekampZassenhausMathlib
