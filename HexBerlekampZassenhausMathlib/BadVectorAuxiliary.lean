import HexBerlekampZassenhausMathlib.BadVector

/-!
Coefficient-facing helper lemmas for the BHKS auxiliary polynomial.

These package the executable `List.range`/`DensePoly.ofCoeffs` shape used by
`BHKS.auxiliaryPolynomial` so downstream norm-bound proofs can rewrite by a
named coefficient formula instead of unfolding the construction.
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

/-- Exact coefficient expansion for the BHKS auxiliary polynomial. -/
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
  unfold BHKS.auxiliaryPolynomial
  rw [Hex.DensePoly.coeff_ofCoeffs_list]
  simpa using
    (list_range_getElem?_map_getD_zero (α := Int)
      (input.degree?.getD 0) j
      (fun j =>
        (List.range liftData.liftedFactors.size).foldl
          (fun acc i =>
            acc +
              vec.getD i 0 *
                (Hex.cldCoeffs input liftData.p liftData.k
                  (liftData.liftedFactors.getD i 0)).getD j 0) 0))

end BHKS

end HexBerlekampZassenhausMathlib
