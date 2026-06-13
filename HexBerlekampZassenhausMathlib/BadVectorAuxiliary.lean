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

/--
Bound the explicit diagonal-correction contribution in the corrected
auxiliary-polynomial squared-l2 estimate by a pointwise bound.
-/
theorem correctionWeightedSum_le_sum
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (corrections : Array Int) (bound : Nat → ℝ)
    (hbound :
      ∀ j, j < input.degree?.getD 0 →
        ((corrections.getD j 0 : ℝ) ^ 2 *
          ((liftData.p : ℝ) ^
            (2 *
              (liftData.k -
                Hex.bhksCoeffCutThreshold liftData.p input j)))) ≤
          bound j) :
    (∑ j ∈ Finset.range (input.degree?.getD 0),
        ((corrections.getD j 0 : ℝ) ^ 2 *
          ((liftData.p : ℝ) ^
            (2 *
              (liftData.k -
                Hex.bhksCoeffCutThreshold liftData.p input j))))) ≤
      ∑ j ∈ Finset.range (input.degree?.getD 0), bound j := by
  exact Finset.sum_le_sum (fun j hj => hbound j (by simpa using hj))

/--
Uniform form of `correctionWeightedSum_le_sum`: if every weighted correction
coordinate is bounded by the same real number, the correction sum is bounded
by `degree * bound`.
-/
theorem correctionWeightedSum_le_degree_mul
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (corrections : Array Int) (bound : ℝ)
    (hbound :
      ∀ j, j < input.degree?.getD 0 →
        ((corrections.getD j 0 : ℝ) ^ 2 *
          ((liftData.p : ℝ) ^
            (2 *
              (liftData.k -
                Hex.bhksCoeffCutThreshold liftData.p input j)))) ≤
          bound) :
    (∑ j ∈ Finset.range (input.degree?.getD 0),
        ((corrections.getD j 0 : ℝ) ^ 2 *
          ((liftData.p : ℝ) ^
            (2 *
              (liftData.k -
                Hex.bhksCoeffCutThreshold liftData.p input j))))) ≤
      (input.degree?.getD 0 : ℝ) * bound := by
  calc
    (∑ j ∈ Finset.range (input.degree?.getD 0),
        ((corrections.getD j 0 : ℝ) ^ 2 *
          ((liftData.p : ℝ) ^
            (2 *
              (liftData.k -
                Hex.bhksCoeffCutThreshold liftData.p input j)))))
        ≤ ∑ _j ∈ Finset.range (input.degree?.getD 0), bound :=
          correctionWeightedSum_le_sum input liftData corrections
            (fun _ => bound) hbound
    _ = (input.degree?.getD 0 : ℝ) * bound := by
      simp [mul_comm]

/--
Canonical pointwise bound for one weighted diagonal-row correction coordinate.

The cut-threshold weight `p ^ (2 (k − ℓ_j))` is at most the uniform `p ^ (2k)`
(since `k − ℓ_j ≤ k` and `p ≥ 1`), so a coordinate bound `c_j ^ 2 ≤ D` lifts to
the uniform weighted bound `D · p ^ (2k)`, exactly the
`correctionWeightedSum_le_degree_mul` input shape with a single canonical value.
-/
theorem correctionWeighted_sq_le_of_coeff_sq_le
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (corrections : Array Int) (D : ℝ) (hp : 1 ≤ liftData.p)
    (hD :
      ∀ j, j < input.degree?.getD 0 →
        ((corrections.getD j 0 : ℝ)) ^ 2 ≤ D)
    (j : Nat) (hj : j < input.degree?.getD 0) :
    ((corrections.getD j 0 : ℝ)) ^ 2 *
        ((liftData.p : ℝ) ^
          (2 * (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j))) ≤
      D * (liftData.p : ℝ) ^ (2 * liftData.k) := by
  have hcj : ((corrections.getD j 0 : ℝ)) ^ 2 ≤ D := hD j hj
  have hp' : (1 : ℝ) ≤ (liftData.p : ℝ) := by exact_mod_cast hp
  have hweight :
      (liftData.p : ℝ) ^
          (2 * (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j)) ≤
        (liftData.p : ℝ) ^ (2 * liftData.k) :=
    pow_le_pow_right₀ hp' (by omega)
  have hweight_nonneg :
      (0 : ℝ) ≤ (liftData.p : ℝ) ^
          (2 * (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j)) := by
    positivity
  have hD_nonneg : (0 : ℝ) ≤ D := le_trans (sq_nonneg _) hcj
  exact mul_le_mul hcj hweight hweight_nonneg hD_nonneg

/--
Pointwise bound for the projected-vector squared sum: if each squared
coordinate is bounded by a real `bound i`, the squared sum is bounded by the
pointwise sum.
-/
theorem projectedVectorSquareSum_le_sum
    {r : Nat} (vec : Array Int) (bound : Fin r → ℝ)
    (hbound :
      ∀ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2) ≤ bound i) :
    (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) ≤
      ∑ i : Fin r, bound i := by
  exact Finset.sum_le_sum (fun i _ => hbound i)

/--
Uniform form of `projectedVectorSquareSum_le_sum`: if every squared coordinate
is bounded by the same real number, the squared sum is bounded by
`factorCount * bound`.
-/
theorem projectedVectorSquareSum_le_factorCount_mul
    {r : Nat} (vec : Array Int) (bound : ℝ)
    (hbound :
      ∀ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2) ≤ bound) :
    (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) ≤
      (r : ℝ) * bound := by
  calc
    (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2))
        ≤ ∑ _i : Fin r, bound :=
          projectedVectorSquareSum_le_sum vec (fun _ => bound) hbound
    _ = (r : ℝ) * bound := by
      simp [mul_comm]

/--
The BHKS auxiliary polynomial (with diagonal-row corrections) lives in the
degree-`n − 1` polynomial space, where `n := input.degree?.getD 0`: its
coefficients vanish for every index at or beyond `n`, so the Mathlib-side
`natDegree` is bounded by `n − 1`.

The bound is vacuous when `n = 0` (Nat subtraction pins both sides at zero);
when `n ≥ 1` it is the natural degree count for the auxiliary polynomial built
from `n` coefficients.

Direct consequence of `coeff_auxiliaryPolynomialWithCorrections` via
`Polynomial.natDegree_le_iff_coeff_eq_zero`.
-/
theorem natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int) :
    (HexPolyZMathlib.toPolynomial
        (BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections)).natDegree ≤
      input.degree?.getD 0 - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [HexPolyZMathlib.coeff_toPolynomial,
    coeff_auxiliaryPolynomialWithCorrections]
  have hN' : ¬ N < input.degree?.getD 0 := by omega
  simp [hN']

/--
Zero-correction specialisation of
`natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le`: the BHKS
auxiliary polynomial associated to a projected vector satisfies
`natDegree ≤ input.degree?.getD 0 − 1`.
-/
theorem natDegree_toPolynomial_auxiliaryPolynomial_le
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) :
    (HexPolyZMathlib.toPolynomial
        (BHKS.auxiliaryPolynomial input liftData vec)).natDegree ≤
      input.degree?.getD 0 - 1 := by
  unfold BHKS.auxiliaryPolynomial
  exact natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le
    input liftData vec #[]

/--
BHKS paper-threshold-compatible looser form of
`natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le`: the auxiliary
polynomial's `natDegree` is bounded by `2n − 1`, the exponent appearing in
`bhksPaperCoeffNormFactorReal core = ‖core‖₂^(2n−1)`.

Follows from the sharper `n − 1` bound by the Nat inequality
`n − 1 ≤ 2n − 1`.
-/
theorem natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le_two_mul_sub_one
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int) :
    (HexPolyZMathlib.toPolynomial
        (BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections)).natDegree ≤
      2 * input.degree?.getD 0 - 1 :=
  (natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le
    input liftData vec corrections).trans (by omega)

/--
Zero-correction specialisation of
`natDegree_toPolynomial_auxiliaryPolynomialWithCorrections_le_two_mul_sub_one`.
-/
theorem natDegree_toPolynomial_auxiliaryPolynomial_le_two_mul_sub_one
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) :
    (HexPolyZMathlib.toPolynomial
        (BHKS.auxiliaryPolynomial input liftData vec)).natDegree ≤
      2 * input.degree?.getD 0 - 1 :=
  (natDegree_toPolynomial_auxiliaryPolynomial_le
    input liftData vec).trans (by omega)

end BHKS

end HexBerlekampZassenhausMathlib
