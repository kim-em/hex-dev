import HexBerlekampZassenhausMathlib.BadVector
import HexBerlekampZassenhausMathlib.BHKSBound

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

/-- Scale and rewrite the body of a left fold whose step adds `g i`: if `c * g i`
agrees with `h i` on every list element, the `c`-scaled fold equals the fold of
`h` with the accumulator seed scaled by `c`. -/
private theorem foldl_add_mul_eq (c : Int) (g h : Nat → Int) (l : List Nat) (a : Int)
    (H : ∀ i ∈ l, c * g i = h i) :
    c * l.foldl (fun acc i => acc + g i) a =
      l.foldl (fun acc i => acc + h i) (c * a) := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hx : c * g x = h x := H x List.mem_cons_self
    have hseed : c * (a + g x) = c * a + h x := by rw [← hx]; ring
    rw [ih (a + g x) (fun i hi => H i (List.mem_cons_of_mem x hi)), hseed]

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
High-bit decomposition of an in-range corrected BHKS auxiliary-polynomial
coefficient.

Scaling coordinate `j` by the per-coordinate cut modulus `p ^ ℓ_j` (where
`ℓ_j = bhksCoeffCutThreshold p input j`) recovers the *uncut* CLD residue
structure: each lifted-factor term `vec_i * cldCoeffs_i` becomes
`vec_i` times the high part
`centeredResiduePow p k q_{i,j} − centeredResiduePow p ℓ_j (centeredResiduePow p k q_{i,j})`
of the quotient coefficient `q_{i,j} = (cldQuotientMod input gᵢ p k).coeff j`,
and the diagonal correction term stays explicit (now carrying the extra
`p ^ ℓ_j` factor).

The `p ^ ℓ_j` weight is essential and must not be dropped: `cldCoeffs` is the
high-bit quotient `psiCut`, *not* a residue representative of the quotient
coefficient modulo `p ^ k`. -/
theorem coeff_auxiliaryPolynomialWithCorrections_high_decomp
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int) (j : Nat)
    (hj : j < input.degree?.getD 0)
    (hb : liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j ≠ 0) :
    ((liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j : Nat) : Int) *
        (BHKS.auxiliaryPolynomialWithCorrections input liftData vec corrections).coeff j =
      (List.range liftData.liftedFactors.size).foldl
        (fun acc i =>
          acc + vec.getD i 0 *
            (Hex.centeredResiduePow liftData.p liftData.k
                ((Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
                    liftData.p liftData.k).coeff j) -
              Hex.centeredResiduePow liftData.p
                  (Hex.bhksCoeffCutThreshold liftData.p input j)
                  (Hex.centeredResiduePow liftData.p liftData.k
                    ((Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
                        liftData.p liftData.k).coeff j)))) 0 -
        corrections.getD j 0 *
            Int.ofNat (liftData.p ^
              (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j)) *
            ((liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j : Nat) : Int) := by
  rw [coeff_auxiliaryPolynomialWithCorrections, if_pos hj, mul_sub]
  congr 1
  · have key := foldl_add_mul_eq
      ((liftData.p ^ Hex.bhksCoeffCutThreshold liftData.p input j : Nat) : Int)
      (fun i => vec.getD i 0 *
        (Hex.cldCoeffs input liftData.p liftData.k
          (liftData.liftedFactors.getD i 0)).getD j 0)
      (fun i => vec.getD i 0 *
        (Hex.centeredResiduePow liftData.p liftData.k
            ((Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
                liftData.p liftData.k).coeff j) -
          Hex.centeredResiduePow liftData.p
              (Hex.bhksCoeffCutThreshold liftData.p input j)
              (Hex.centeredResiduePow liftData.p liftData.k
                ((Hex.cldQuotientMod input (liftData.liftedFactors.getD i 0)
                    liftData.p liftData.k).coeff j))))
      (List.range liftData.liftedFactors.size) 0
      (fun i _ => by
        have hd := Hex.cldQuotientMod_coeff_decomp_of_lt input
          (liftData.liftedFactors.getD i 0) liftData.p liftData.k j hj hb
        linear_combination -(vec.getD i 0) * hd)
    rw [mul_zero] at key
    exact key
  · ring

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

/--
The squared `l2norm` of the corrected BHKS auxiliary polynomial is bounded by
the CLD column-norm bound.

The genuine `l2norm` sums squared coefficients over all indices, whereas the
shortness certificate's `coeffSqSum_le` only controls the truncated sum over
`Finset.range n` (`n := input.degree?.getD 0`). The two agree because every
coefficient at index `≥ n` vanishes
(`coeff_auxiliaryPolynomialWithCorrections`), so the support is contained in
`Finset.range n` and the tail contributes nothing.
-/
theorem l2norm_sq_toPolynomial_auxiliaryPolynomialWithCorrections_le
    {input : Hex.ZPoly} {liftData : Hex.LiftData}
    {vec corrections : Array Int}
    (C : ScaledShortnessCertificate input liftData vec corrections) :
    (HexPolyZMathlib.l2norm
        (HexPolyZMathlib.toPolynomial
          (auxiliaryPolynomialWithCorrections input liftData vec corrections))) ^ 2
      ≤ (cldColumnNormBound input liftData.p : ℝ) := by
  set n := input.degree?.getD 0 with hn
  set p := HexPolyZMathlib.toPolynomial
      (auxiliaryPolynomialWithCorrections input liftData vec corrections) with hp
  have hsupp : p.support ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_range]
    by_contra hge
    have hzero : p.coeff i = 0 := by
      rw [hp, HexPolyZMathlib.coeff_toPolynomial,
        coeff_auxiliaryPolynomialWithCorrections, if_neg (by omega : ¬ i < n)]
    exact (Polynomial.mem_support_iff.mp hi) hzero
  have hsq : (HexPolyZMathlib.l2norm p) ^ 2 =
      ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := by
    unfold HexPolyZMathlib.l2norm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum_le : ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range n, (p.coeff i : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsupp (fun i _ _ => sq_nonneg _)
  have heq : ∑ i ∈ Finset.range n, (p.coeff i : ℝ) ^ 2 =
      ∑ j ∈ Finset.range n,
        ((((auxiliaryPolynomialWithCorrections input liftData vec corrections).coeff j :
          ℤ) : ℝ) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hp, HexPolyZMathlib.coeff_toPolynomial]
  calc
    (HexPolyZMathlib.l2norm p) ^ 2
        = ∑ i ∈ p.support, (p.coeff i : ℝ) ^ 2 := hsq
    _ ≤ ∑ i ∈ Finset.range n, (p.coeff i : ℝ) ^ 2 := hsum_le
    _ = ∑ j ∈ Finset.range n,
          ((((auxiliaryPolynomialWithCorrections input liftData vec corrections).coeff j :
            ℤ) : ℝ) ^ 2) := heq
    _ ≤ (cldColumnNormBound input liftData.p : ℝ) := C.coeffSqSum_le

/--
Zero-correction specialisation of
`l2norm_sq_toPolynomial_auxiliaryPolynomialWithCorrections_le`: the form
consumed downstream where the auxiliary polynomial carries no diagonal-row
corrections.
-/
theorem l2norm_sq_toPolynomial_auxiliaryPolynomial_le
    {input : Hex.ZPoly} {liftData : Hex.LiftData} {vec : Array Int}
    (C : ScaledShortnessCertificate input liftData vec #[]) :
    (HexPolyZMathlib.l2norm
        (HexPolyZMathlib.toPolynomial
          (auxiliaryPolynomial input liftData vec))) ^ 2
      ≤ (cldColumnNormBound input liftData.p : ℝ) := by
  unfold auxiliaryPolynomial
  exact l2norm_sq_toPolynomial_auxiliaryPolynomialWithCorrections_le C

/--
Joint BHKS auxiliary domination from the executable CLD square bound.

This is the reusable paper-threshold bridge for BHKS §5: a generic auxiliary
norm whose square is bounded by `cldColumnNormBound`, and whose degree is at
most `n - 1`, satisfies the joint product bound
`‖core‖₂^auxDegree * auxNorm^n ≤ bhksPaperThresholdReal core 2`.
-/
theorem jointAux_le_paperThreshold
    (core : Hex.ZPoly) (p : Nat) {auxNorm : ℝ} {auxDegree : Nat}
    (hdeg : 2 ≤ bhksDegree core)
    (hcoreNorm :
      1 < HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial core))
    (haux_sq : auxNorm ^ 2 ≤ (cldColumnNormBound core p : ℝ))
    (hauxDegree : auxDegree ≤ bhksDegree core - 1)
    (haux_nonneg : 0 ≤ auxNorm) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial core)) ^ auxDegree *
        auxNorm ^ bhksDegree core ≤ bhksPaperThresholdReal core 2 := by
  let n := bhksDegree core
  let N := HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial core)
  let L : ℝ := Hex.ZPoly.coeffL2NormBound core
  have hn : 2 ≤ n := by simpa [n] using hdeg
  have hN_nonneg : 0 ≤ N := by
    unfold N HexPolyZMathlib.l2norm
    exact Real.sqrt_nonneg _
  have hN_one : 1 ≤ N := le_of_lt hcoreNorm
  have hL_nonneg : 0 ≤ L := by
    unfold L
    exact_mod_cast Nat.zero_le (Hex.ZPoly.coeffL2NormBound core)
  have hcld_real :
      (cldColumnNormBound core p : ℝ) ≤
        (n : ℝ) ^ 2 * L ^ 2 * (4 : ℝ) ^ (n - 1) := by
    have hcld := cldColumnNormBound_le core p
    have hcld' :
        (cldColumnNormBound core p : ℝ) ≤
          ((n ^ 2 * (Hex.ZPoly.coeffL2NormBound core) ^ 2 *
            4 ^ (n - 1) : Nat) : ℝ) := by
      simpa [n, bhksDegree] using (by exact_mod_cast hcld)
    simpa [L, Nat.cast_mul, Nat.cast_pow] using hcld'
  have haux_sq_bound :
      auxNorm ^ 2 ≤ (n : ℝ) ^ 2 * L ^ 2 * (4 : ℝ) ^ (n - 1) :=
    haux_sq.trans hcld_real
  have htwo_pow_nonneg : 0 ≤ (2 : ℝ) ^ (n - 1) := by positivity
  have haux_bound_sq :
      auxNorm ^ 2 ≤ ((n : ℝ) * L * (2 : ℝ) ^ (n - 1)) ^ 2 := by
    calc
      auxNorm ^ 2 ≤ (n : ℝ) ^ 2 * L ^ 2 * (4 : ℝ) ^ (n - 1) := haux_sq_bound
      _ = ((n : ℝ) * L * (2 : ℝ) ^ (n - 1)) ^ 2 := by
          rw [show (4 : ℝ) ^ (n - 1) = ((2 : ℝ) ^ (n - 1)) ^ 2 by
            calc
              (4 : ℝ) ^ (n - 1) = ((2 : ℝ) ^ 2) ^ (n - 1) := by norm_num
              _ = (2 : ℝ) ^ (2 * (n - 1)) := by rw [pow_mul]
              _ = (2 : ℝ) ^ ((n - 1) * 2) := by rw [Nat.mul_comm]
              _ = ((2 : ℝ) ^ (n - 1)) ^ 2 := by rw [pow_mul]]
          ring
  have haux_bound_nonneg : 0 ≤ (n : ℝ) * L * (2 : ℝ) ^ (n - 1) :=
    mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le n) hL_nonneg)
      htwo_pow_nonneg
  have haux_bound : auxNorm ≤ (n : ℝ) * L * (2 : ℝ) ^ (n - 1) :=
    le_of_sq_le_sq haux_bound_sq haux_bound_nonneg
  have haux_pow :
      auxNorm ^ n ≤ ((n : ℝ) * L * (2 : ℝ) ^ (n - 1)) ^ n :=
    pow_le_pow_left₀ haux_nonneg haux_bound n
  have hN_pow :
      N ^ auxDegree ≤ N ^ (n - 1) :=
    pow_le_pow_right₀ hN_one hauxDegree
  have hjoint_bound :
      N ^ auxDegree * auxNorm ^ n ≤
        N ^ (n - 1) * ((n : ℝ) * L * (2 : ℝ) ^ (n - 1)) ^ n := by
    exact mul_le_mul hN_pow haux_pow (pow_nonneg haux_nonneg _) (pow_nonneg hN_nonneg _)
  have habsorb :
      (n : ℝ) ^ (n - 1) * L ^ n ≤
        (2 : ℝ) ^ (n * n + n) * N ^ n *
          (Real.log N) ^ n := by
    simpa [n, N, L] using
      coeffL2NormBound_absorb_log_of_one_lt core hdeg hcoreNorm
  have hbudget :
      N ^ (n - 1) * ((n : ℝ) * L * (2 : ℝ) ^ (n - 1)) ^ n ≤
        bhksPaperThresholdReal core 2 := by
    have hn_pos : 1 ≤ n := by omega
    have hn_pow :
        (n : ℝ) ^ n = (n : ℝ) * (n : ℝ) ^ (n - 1) := by
      calc
        (n : ℝ) ^ n = (n : ℝ) ^ ((n - 1) + 1) := by congr 1; omega
        _ = (n : ℝ) ^ (n - 1) * (n : ℝ) := by rw [pow_succ]
        _ = (n : ℝ) * (n : ℝ) ^ (n - 1) := by ring
    have htwo_pow :
        ((2 : ℝ) ^ (n - 1)) ^ n = (2 : ℝ) ^ (n * (n - 1)) := by
      calc
        ((2 : ℝ) ^ (n - 1)) ^ n = (2 : ℝ) ^ ((n - 1) * n) := by
          rw [pow_mul]
        _ = (2 : ℝ) ^ (n * (n - 1)) := by rw [Nat.mul_comm]
    calc
      N ^ (n - 1) * ((n : ℝ) * L * (2 : ℝ) ^ (n - 1)) ^ n
          = (n : ℝ) *
              ((n : ℝ) ^ (n - 1) * L ^ n) *
              (2 : ℝ) ^ (n * (n - 1)) *
              N ^ (n - 1) := by
            rw [mul_pow, mul_pow]
            rw [hn_pow, htwo_pow]
            ring
      _ ≤ (n : ℝ) *
              ((2 : ℝ) ^ (n * n + n) * N ^ n * (Real.log N) ^ n) *
              (2 : ℝ) ^ (n * (n - 1)) *
              N ^ (n - 1) := by
            have hn_nonneg_real : 0 ≤ (n : ℝ) := by
              exact_mod_cast Nat.zero_le n
            have hstep₁ :
                (n : ℝ) * ((n : ℝ) ^ (n - 1) * L ^ n) ≤
                  (n : ℝ) *
                    ((2 : ℝ) ^ (n * n + n) * N ^ n * (Real.log N) ^ n) :=
              mul_le_mul_of_nonneg_left habsorb hn_nonneg_real
            have hstep₂ :
                (n : ℝ) * ((n : ℝ) ^ (n - 1) * L ^ n) *
                    (2 : ℝ) ^ (n * (n - 1)) ≤
                  (n : ℝ) *
                    ((2 : ℝ) ^ (n * n + n) * N ^ n * (Real.log N) ^ n) *
                    (2 : ℝ) ^ (n * (n - 1)) :=
              mul_le_mul_of_nonneg_right hstep₁ (by positivity)
            exact mul_le_mul_of_nonneg_right hstep₂
              (pow_nonneg hN_nonneg (n - 1))
      _ = (n : ℝ) * (2 : ℝ) ^ (2 * (n * n)) *
              N ^ (2 * n - 1) * (Real.log N) ^ n := by
            have hexp : n * n + n + n * (n - 1) = 2 * (n * n) := by
              cases n with
              | zero => omega
              | succ k =>
                  simp
                  ring
            have hNexp : n + (n - 1) = 2 * n - 1 := by
              cases n with
              | zero => omega
              | succ k =>
                  simp
                  omega
            calc
              (n : ℝ) *
                    ((2 : ℝ) ^ (n * n + n) * N ^ n * (Real.log N) ^ n) *
                    (2 : ℝ) ^ (n * (n - 1)) * N ^ (n - 1)
                  =
                  (n : ℝ) *
                    ((2 : ℝ) ^ (n * n + n) * (2 : ℝ) ^ (n * (n - 1))) *
                    (N ^ n * N ^ (n - 1)) * (Real.log N) ^ n := by
                    ring
              _ =
                  (n : ℝ) * (2 : ℝ) ^ (2 * (n * n)) *
                    N ^ (2 * n - 1) * (Real.log N) ^ n := by
                    rw [← pow_add, hexp, ← pow_add, hNexp]
      _ = bhksPaperThresholdReal core 2 := by
            have hconst :
                (4 : ℝ) ^ (n * n) = (2 : ℝ) ^ (2 * (n * n)) := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
              exact (pow_mul (2 : ℝ) 2 (n * n)).symm
            unfold bhksPaperThresholdReal bhksPaperDegreeFactorReal
              bhksPaperConstantFactorReal bhksPaperCoeffNormFactorReal
              bhksPaperLogFactorReal
            rw [show (2 : ℝ) * 2 = 4 by norm_num, hconst]
  exact hjoint_bound.trans hbudget

/--
Concrete zero-correction BHKS auxiliary-polynomial domination at `C = 2`.

This specializes `jointAux_le_paperThreshold` to the executable auxiliary
polynomial `BHKS.auxiliaryPolynomial`.  The degree and squared-l2 hypotheses
are discharged by the concrete auxiliary-polynomial support and CLD-column
facts, so downstream recovery code can consume the joint product directly.
-/
theorem auxiliary_le_paperThreshold
    (core : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int)
    (C : ScaledShortnessCertificate core liftData vec #[])
    (hdeg : 2 ≤ bhksDegree core)
    (hcoreNorm :
      1 < HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial core)) :
    (HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial core)) ^
          (HexPolyZMathlib.toPolynomial
            (BHKS.auxiliaryPolynomial core liftData vec)).natDegree *
        (HexPolyZMathlib.l2norm
          (HexPolyZMathlib.toPolynomial
            (BHKS.auxiliaryPolynomial core liftData vec))) ^
          bhksDegree core ≤
      bhksPaperThresholdReal core 2 := by
  exact
    jointAux_le_paperThreshold core liftData.p hdeg hcoreNorm
      (l2norm_sq_toPolynomial_auxiliaryPolynomial_le C)
      (natDegree_toPolynomial_auxiliaryPolynomial_le core liftData vec)
      (by unfold HexPolyZMathlib.l2norm; exact Real.sqrt_nonneg _)

end BHKS

end HexBerlekampZassenhausMathlib
