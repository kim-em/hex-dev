import HexBerlekampZassenhaus.Basic
import HexBerlekampZassenhausMathlib.Lattice
import HexBerlekampZassenhausMathlib.Resultant

/-!
Abstract resultant/divisibility layer for the BHKS bad-vector argument.

The executable CLD/lattice objects are deliberately absent from this module.
Later BHKS termination work can instantiate `BadVectorResultantData` with the
polynomial associated to a lattice vector, then use the packaged lower and
upper bounds without reopening the resultant API.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/--
Proof-facing data carried by the BHKS bad-vector route.

`f` is the input polynomial and `H` is the auxiliary polynomial extracted from
the bad vector.  The hypotheses say that the transported pair is coprime over
`ℚ` and that the modular construction forces a `p^(a*d)` divisibility of the
integer resultant.
-/
structure BadVectorResultantData where
  f : Polynomial ℤ
  H : Polynomial ℤ
  p : Nat
  a : Nat
  d : Nat
  p_pos : 0 < p
  d_pos : 0 < d
  coprime_over_rat :
    IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ))
  resultant_divisible :
    ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H

namespace BadVectorResultantData

/-- The integer resultant attached to bad-vector proof data. -/
def resultant (D : BadVectorResultantData) : ℤ :=
  Polynomial.resultant D.f D.H

/-- The modular lower-bound divisor attached to bad-vector proof data. -/
def divisor (D : BadVectorResultantData) : Nat :=
  D.p ^ (D.a * D.d)

theorem resultant_ne_zero (D : BadVectorResultantData) :
    D.resultant ≠ 0 := by
  exact int_resultant_ne_zero_of_coprime_over_rat D.f D.H D.coprime_over_rat

theorem divisor_pos (D : BadVectorResultantData) :
    0 < D.divisor := by
  exact pow_pos D.p_pos _

/--
The modular divisibility hypothesis gives the arithmetic lower bound on the
absolute value of the nonzero integer resultant.
-/
theorem divisor_le_resultant_natAbs (D : BadVectorResultantData) :
    D.divisor ≤ Int.natAbs D.resultant := by
  have hdiv : ((D.divisor : Nat) : ℤ) ∣ D.resultant := by
    simpa [divisor, resultant] using D.resultant_divisible
  have hnonzero : D.resultant ≠ 0 := D.resultant_ne_zero
  simpa [divisor] using Int.natAbs_le_of_dvd_ne_zero hdiv hnonzero

/--
Real-valued lower bound used when comparing the BHKS modular divisibility
against Hadamard's resultant upper bound.
-/
theorem divisor_real_le_abs_resultant (D : BadVectorResultantData) :
    (D.divisor : ℝ) ≤ |((D.resultant : ℤ) : ℝ)| := by
  have h : (D.divisor : ℝ) ≤ (Int.natAbs D.resultant : ℝ) := by
    exact_mod_cast D.divisor_le_resultant_natAbs
  simpa [Nat.cast_natAbs] using h

/-- Existing Sylvester/Hadamard bound specialized to bad-vector data. -/
theorem abs_resultant_le_l2norm_pow (D : BadVectorResultantData) :
    |((D.resultant : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
        (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree := by
  simpa [resultant] using
    HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow D.f D.H

/--
Combined BHKS bad-vector resultant comparison: the modular lower bound is at
most the Hadamard/l2norm upper bound.
-/
theorem divisor_real_le_l2norm_pow (D : BadVectorResultantData) :
    (D.divisor : ℝ) ≤
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
        (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree :=
  le_trans D.divisor_real_le_abs_resultant D.abs_resultant_le_l2norm_pow

/--
If the Hadamard/l2norm upper bound is strictly below the modular divisor, the
packaged bad-vector resultant data is contradictory.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor
    (D : BadVectorResultantData)
    (hlt :
      (HexPolyZMathlib.l2norm D.f) ^ D.H.natDegree *
          (HexPolyZMathlib.l2norm D.H) ^ D.f.natDegree <
        (D.divisor : ℝ)) :
    False :=
  (not_lt_of_ge D.divisor_real_le_l2norm_pow) hlt

/--
Parameter-style wrapper for later callers that do not want to construct the
record explicitly in theorem statements.
-/
theorem badVector_resultant_bounds
    (f H : Polynomial ℤ) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)))
    (hdiv : ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H) :
    (p ^ (a * d) : ℝ) ≤
      |((Polynomial.resultant f H : ℤ) : ℝ)| ∧
    |((Polynomial.resultant f H : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
        (HexPolyZMathlib.l2norm H) ^ f.natDegree := by
  let D : BadVectorResultantData :=
    { f := f
      H := H
      p := p
      a := a
      d := d
      p_pos := hp
      d_pos := hd
      coprime_over_rat := hcoprime
      resultant_divisible := hdiv }
  exact ⟨by simpa [D, divisor, resultant] using D.divisor_real_le_abs_resultant,
    by simpa [D, resultant] using D.abs_resultant_le_l2norm_pow⟩

/--
Parameter-style contradiction wrapper for callers that have the raw bad-vector
resultant hypotheses rather than a `BadVectorResultantData` record.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor_params
    (f H : Polynomial ℤ) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime (f.map (Int.castRingHom ℚ)) (H.map (Int.castRingHom ℚ)))
    (hdiv : ((p ^ (a * d) : Nat) : ℤ) ∣ Polynomial.resultant f H)
    (hlt :
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
          (HexPolyZMathlib.l2norm H) ^ f.natDegree <
        (p ^ (a * d) : ℝ)) :
    False := by
  let D : BadVectorResultantData :=
    { f := f
      H := H
      p := p
      a := a
      d := d
      p_pos := hp
      d_pos := hd
      coprime_over_rat := hcoprime
      resultant_divisible := hdiv }
  exact D.no_badVector_of_l2norm_upper_lt_divisor (by
    simpa [D, divisor] using hlt)

end BadVectorResultantData

/--
Proof-facing witness tying an executable BHKS bad vector back to the abstract
integer-resultant data used by the termination proof.

The executable fields name the original `ZPoly`, the Hensel lift data, the
all-coefficients CLD lattice, the projected `L'` rows, and the selected local
factor index/degree.  The auxiliary polynomial is stored as a `Hex.ZPoly`; the
Mathlib-facing polynomial used in resultants is `auxiliaryPolynomial`.
-/
structure ExecutableBadVectorWitness where
  input : Hex.ZPoly
  liftData : Hex.LiftData
  lattice : Hex.BhksLatticeBasis
  projectedRows : Hex.BhksProjectedRows
  localFactorIndex : Nat
  localFactorDegree : Nat
  H : Hex.ZPoly
  lattice_matches_lift :
    lattice =
      Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors
  projected_factor_count :
    projectedRows.factorCount = lattice.factorCount

namespace ExecutableBadVectorWitness

/-- The input polynomial transported to Mathlib's `Polynomial ℤ`. -/
def inputPolynomial (W : ExecutableBadVectorWitness) : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial W.input

/-- The auxiliary bad-vector polynomial transported to Mathlib's `Polynomial ℤ`. -/
def auxiliaryPolynomial (W : ExecutableBadVectorWitness) : Polynomial ℤ :=
  HexPolyZMathlib.toPolynomial W.H

/-- The selected lifted factor, if the executable array contains the index. -/
def selectedLiftedFactor (W : ExecutableBadVectorWitness) : Hex.ZPoly :=
  W.liftData.liftedFactors.getD W.localFactorIndex 0

/--
Package an executable bad-vector witness and the remaining BHKS local
coprimality/divisibility hypotheses as abstract resultant data.
-/
def toResultantData
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    BadVectorResultantData where
  f := W.inputPolynomial
  H := W.auxiliaryPolynomial
  p := W.liftData.p
  a := W.liftData.k
  d := W.localFactorDegree
  p_pos := hp
  d_pos := hd
  coprime_over_rat := hcoprime
  resultant_divisible := hdiv

/--
Executable bad-vector packaging theorem: once later BHKS work supplies the
local coprimality and modular-divisibility hypotheses, the existing resultant
lower/upper-bound theorem applies to the transported executable data.
-/
theorem badVector_resultant_bounds
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ∧
    |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree := by
  simpa [inputPolynomial, auxiliaryPolynomial] using
    BadVectorResultantData.badVector_resultant_bounds
      W.inputPolynomial W.auxiliaryPolynomial
      W.liftData.p W.liftData.k W.localFactorDegree
      hp hd hcoprime hdiv

/--
Executable bad-vector contradiction wrapper: the transported witness cannot
exist when its Hadamard/l2norm upper bound is already below the modular divisor.
-/
theorem no_badVector_of_l2norm_upper_lt_divisor
    (W : ExecutableBadVectorWitness)
    (hp : 0 < W.liftData.p)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        ((W.inputPolynomial).map (Int.castRingHom ℚ))
        ((W.auxiliaryPolynomial).map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
          (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree <
        (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    False := by
  simpa [inputPolynomial, auxiliaryPolynomial] using
    BadVectorResultantData.no_badVector_of_l2norm_upper_lt_divisor_params
      W.inputPolynomial W.auxiliaryPolynomial
      W.liftData.p W.liftData.k W.localFactorDegree
      hp hd hcoprime hdiv hlt

end ExecutableBadVectorWitness

namespace BHKS

/--
The BHKS auxiliary polynomial `H_v` associated to an integer vector `v` over
the lifted local factors, with explicit diagonal-row correction coordinates.

The all-coefficients BHKS lattice basis has block form
`[I_r | A ; 0 | diag(p^(a - ell_j))]`.  A projected vector records only the
first `r` coordinates, so the polynomial attached to a full lattice vector must
subtract the diagonal-row correction coordinates from the CLD block.  The
`corrections` array stores those diagonal-row coefficients, one per
coefficient index `j`.
-/
def auxiliaryPolynomialWithCorrections
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (vec corrections : Array Int) : Hex.ZPoly :=
  let n := input.degree?.getD 0
  let r := liftData.liftedFactors.size
  let coeffs : List Int := (List.range n).map fun j =>
    let cldSum :=
      (List.range r).foldl (fun acc i =>
        acc +
          vec.getD i 0 *
            (Hex.cldCoeffs input liftData.p liftData.k
                (liftData.liftedFactors.getD i 0)).getD j 0) 0
    cldSum -
      corrections.getD j 0 *
        Int.ofNat (liftData.p ^ (liftData.k - Hex.bhksCoeffCutThreshold liftData.p input j))
  Hex.DensePoly.ofCoeffs coeffs.toArray

/--
Compatibility wrapper for callers that have no diagonal-row correction data.

Downstream BHKS bad-vector construction should prefer
`auxiliaryPolynomialWithCorrections` once it has recovered the full lattice-row
coordinates; this wrapper is the zero-correction specialization used by the
existing resultant-bound surface.
-/
def auxiliaryPolynomial
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) : Hex.ZPoly :=
  auxiliaryPolynomialWithCorrections input liftData vec #[]

/--
Column-sum-squared packaging used by the BHKS Lemma 3.2 l2-norm bound on the
auxiliary polynomial.  Sums `(bhksCoeffBound input j)^2` over the coefficient
indices `j < n` of the input, where `n := input.degree?.getD 0`.

The prime `p` is carried for API symmetry with the surrounding BHKS column
infrastructure; the body does not depend on it.
-/
def cldColumnNormBound (input : Hex.ZPoly) (_p : Nat) : Nat :=
  let n := input.degree?.getD 0
  (List.range n).foldl (fun acc j => acc + (Hex.bhksCoeffBound input j) ^ 2) 0

private theorem range_foldl_add_int_eq_sum (m : Nat) (g : Nat → Int) :
    (List.range m).foldl (fun acc i => acc + g i) 0 = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

private theorem range_foldl_add_nat_pow_eq_sum (m : Nat) (g : Nat → Nat) :
    (List.range m).foldl (fun acc i => acc + (g i) ^ 2) 0 =
      ∑ i ∈ Finset.range m, (g i) ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

private theorem auxiliaryPolynomial_coeff_eq
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) (j : Nat) :
    (BHKS.auxiliaryPolynomial input liftData vec).coeff j =
      if j < input.degree?.getD 0 then
        ∑ i ∈ Finset.range liftData.liftedFactors.size,
          vec.getD i 0 *
            (Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0
      else 0 := by
  unfold BHKS.auxiliaryPolynomial BHKS.auxiliaryPolynomialWithCorrections
  rw [Hex.DensePoly.coeff_ofCoeffs_list]
  have hempty : (#[] : Array Int).getD j 0 = 0 := by
    simp [Array.getD]
  by_cases hjn : j < input.degree?.getD 0
  · rw [if_pos hjn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show (List.range _)[j]? = some j from List.getElem?_range hjn]
    simp only [Option.map_some, Option.getD_some]
    rw [hempty]
    simp only [zero_mul, sub_zero]
    exact range_foldl_add_int_eq_sum _ _
  · rw [if_neg hjn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    have hnone : (List.range (input.degree?.getD 0))[j]? = none := by
      rw [List.getElem?_eq_none_iff]
      simpa using Nat.le_of_not_lt hjn
    rw [hnone]
    rfl

/--
Per-coefficient Cauchy–Schwarz bound for the BHKS auxiliary polynomial.

The hypothesis `h` packages the BHKS Lemma 5.1 column bound on every
executable `cldCoeffs` entry uniformly over the lifted factor index `i` and
the coefficient index `j`.  Under that hypothesis, the squared j-th
coefficient of `auxiliaryPolynomial input liftData vec` is bounded by
`‖v‖₂² · r · (bhksCoeffBound input j)²`, where `r` is the number of lifted
factors.

The leading `r` factor comes from `Σ_{i<r} c_{i,j}² ≤ r · max_i c_{i,j}²`
combined with `(Σ_{i<r} v_i c_{i,j})² ≤ (Σ v_i²)(Σ c_{i,j}²)` by
Cauchy–Schwarz.
-/
theorem auxiliaryPolynomial_coeff_sq_le
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int)
    (h : ∀ (i : Nat), i < liftData.liftedFactors.size → ∀ (j : Nat),
        ((Hex.cldCoeffs input liftData.p liftData.k
            (liftData.liftedFactors.getD i 0)).getD j 0).natAbs ≤
          Hex.bhksCoeffBound input j)
    (j : Nat) :
    (((BHKS.auxiliaryPolynomial input liftData vec).coeff j : ℝ)) ^ 2 ≤
      (∑ i : Fin liftData.liftedFactors.size,
          ((vec.getD i.val 0 : ℝ) ^ 2)) *
        ((liftData.liftedFactors.size : ℝ) *
          ((Hex.bhksCoeffBound input j : ℝ) ^ 2)) := by
  set r := liftData.liftedFactors.size with hr_def
  set B : ℝ := (Hex.bhksCoeffBound input j : ℝ) with hB_def
  rw [auxiliaryPolynomial_coeff_eq]
  have hsum_v_range_eq : (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) =
      ∑ i ∈ Finset.range r, (vec.getD i 0 : ℝ) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun i => ((vec.getD i 0 : ℝ) ^ 2)) r
  by_cases hjn : j < input.degree?.getD 0
  · rw [if_pos hjn]
    set v : Nat → ℝ := fun i => (vec.getD i 0 : ℝ) with hv_def
    set c : Nat → ℝ := fun i => ((Hex.cldCoeffs input liftData.p liftData.k
        (liftData.liftedFactors.getD i 0)).getD j 0 : ℝ) with hc_def
    have hsum_eq :
        (((∑ i ∈ Finset.range r, vec.getD i 0 *
              (Hex.cldCoeffs input liftData.p liftData.k
                (liftData.liftedFactors.getD i 0)).getD j 0 : ℤ)) : ℝ) =
          ∑ i ∈ Finset.range r, v i * c i := by
      push_cast
      rfl
    rw [hsum_eq, hsum_v_range_eq]
    have hCS : (∑ i ∈ Finset.range r, v i * c i) ^ 2 ≤
        (∑ i ∈ Finset.range r, v i ^ 2) * ∑ i ∈ Finset.range r, c i ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ v c
    have hc_each : ∀ i ∈ Finset.range r, c i ^ 2 ≤ B ^ 2 := by
      intro i hi
      have hi' : i < r := Finset.mem_range.mp hi
      have habs := h i hi' j
      have hnat_real :
          (((Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0).natAbs : ℝ) ≤ B := by
        show (((Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0).natAbs : ℝ) ≤
          ((Hex.bhksCoeffBound input j : Nat) : ℝ)
        exact_mod_cast habs
      have hnatAbs_real_nonneg :
          (0 : ℝ) ≤ (((Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0).natAbs : ℝ) := by
        exact_mod_cast Nat.zero_le _
      have h_sq_eq : c i ^ 2 =
          (((Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0).natAbs : ℝ) ^ 2 := by
        show (((Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0 : ℤ) : ℝ) ^ 2 = _
        have hnat_eq_abs :
            (((Hex.cldCoeffs input liftData.p liftData.k
              (liftData.liftedFactors.getD i 0)).getD j 0).natAbs : ℝ) =
              |(((Hex.cldCoeffs input liftData.p liftData.k
                (liftData.liftedFactors.getD i 0)).getD j 0 : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [hnat_eq_abs]
        exact (sq_abs _).symm
      rw [h_sq_eq]
      exact pow_le_pow_left₀ hnatAbs_real_nonneg hnat_real 2
    have hsum_c_le : ∑ i ∈ Finset.range r, c i ^ 2 ≤ (r : ℝ) * B ^ 2 := by
      calc ∑ i ∈ Finset.range r, c i ^ 2
          ≤ ∑ i ∈ Finset.range r, B ^ 2 := Finset.sum_le_sum hc_each
        _ = (r : ℝ) * B ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hv_nonneg : 0 ≤ ∑ i ∈ Finset.range r, v i ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    calc (∑ i ∈ Finset.range r, v i * c i) ^ 2
        ≤ (∑ i ∈ Finset.range r, v i ^ 2) * ∑ i ∈ Finset.range r, c i ^ 2 := hCS
      _ ≤ (∑ i ∈ Finset.range r, v i ^ 2) * ((r : ℝ) * B ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_c_le hv_nonneg
  · rw [if_neg hjn, Int.cast_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)]
    apply mul_nonneg
    · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact sq_nonneg _

/--
BHKS Lemma 3.2 squared-l2-norm bound for the auxiliary polynomial.

The transported Mathlib polynomial's squared `l2norm` is bounded by
`‖v‖₂² · r · cldColumnNormBound input`, where `r` is the number of lifted
factors and `cldColumnNormBound input p = Σ_{j<n} (bhksCoeffBound input j)²`
is the column-sum-squared packaging defined above.

This consumes the per-coefficient bound `auxiliaryPolynomial_coeff_sq_le` and
the BHKS Lemma 5.1 column hypothesis `h`; the leading `r` factor is
inherited from the per-coefficient Cauchy–Schwarz step.
-/
theorem auxiliaryPolynomial_l2norm_sq_le
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int)
    (h : ∀ (i : Nat), i < liftData.liftedFactors.size → ∀ (j : Nat),
        ((Hex.cldCoeffs input liftData.p liftData.k
            (liftData.liftedFactors.getD i 0)).getD j 0).natAbs ≤
          Hex.bhksCoeffBound input j) :
    (HexPolyZMathlib.l2norm
        (HexPolyZMathlib.toPolynomial
          (BHKS.auxiliaryPolynomial input liftData vec))) ^ 2 ≤
      (∑ i : Fin liftData.liftedFactors.size,
          ((vec.getD i.val 0 : ℝ) ^ 2)) *
        ((liftData.liftedFactors.size : ℝ) *
          (BHKS.cldColumnNormBound input liftData.p : ℝ)) := by
  set p := HexPolyZMathlib.toPolynomial (BHKS.auxiliaryPolynomial input liftData vec)
  set n := input.degree?.getD 0 with hn_def
  set r := liftData.liftedFactors.size with hr_def
  have hcoeff_eq : ∀ j, p.coeff j =
      (BHKS.auxiliaryPolynomial input liftData vec).coeff j := by
    intro j
    show (HexPolyZMathlib.toPolynomial _).coeff j = _
    exact HexPolyZMathlib.coeff_toPolynomial _ _
  have hcoeff_zero_above : ∀ j, n ≤ j → p.coeff j = 0 := by
    intro j hj
    rw [hcoeff_eq, auxiliaryPolynomial_coeff_eq]
    rw [if_neg (by omega)]
  have hsupport : p.support ⊆ Finset.range n := by
    intro j hj
    by_contra hjn
    have hge : n ≤ j := by simpa [Finset.mem_range] using hjn
    exact (Polynomial.mem_support_iff.mp hj) (hcoeff_zero_above j hge)
  have hl2norm_sq : (HexPolyZMathlib.l2norm p) ^ 2 =
      ∑ j ∈ p.support, (p.coeff j : ℝ) ^ 2 := by
    unfold HexPolyZMathlib.l2norm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  have hsum_le : ∑ j ∈ p.support, (p.coeff j : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.range n, (p.coeff j : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsupport
      (fun j _ _ => sq_nonneg _)
  have hcoeff_each : ∀ j ∈ Finset.range n,
      (p.coeff j : ℝ) ^ 2 ≤
        (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
          ((r : ℝ) * ((Hex.bhksCoeffBound input j : ℝ) ^ 2)) := by
    intro j _
    rw [hcoeff_eq]
    exact auxiliaryPolynomial_coeff_sq_le input liftData vec h j
  have hsum_bd : ∑ j ∈ Finset.range n, (p.coeff j : ℝ) ^ 2 ≤
      ∑ j ∈ Finset.range n,
        ((∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
          ((r : ℝ) * ((Hex.bhksCoeffBound input j : ℝ) ^ 2))) :=
    Finset.sum_le_sum hcoeff_each
  have hsum_factor : ∑ j ∈ Finset.range n,
        ((∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
          ((r : ℝ) * ((Hex.bhksCoeffBound input j : ℝ) ^ 2))) =
      (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
        ((r : ℝ) * ∑ j ∈ Finset.range n,
          ((Hex.bhksCoeffBound input j : ℝ) ^ 2)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hcldcol : (∑ j ∈ Finset.range n, ((Hex.bhksCoeffBound input j : ℝ) ^ 2)) =
      (BHKS.cldColumnNormBound input liftData.p : ℝ) := by
    unfold BHKS.cldColumnNormBound
    rw [range_foldl_add_nat_pow_eq_sum]
    push_cast
    rfl
  calc (HexPolyZMathlib.l2norm p) ^ 2
      = ∑ j ∈ p.support, (p.coeff j : ℝ) ^ 2 := hl2norm_sq
    _ ≤ ∑ j ∈ Finset.range n, (p.coeff j : ℝ) ^ 2 := hsum_le
    _ ≤ ∑ j ∈ Finset.range n,
        ((∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
          ((r : ℝ) * ((Hex.bhksCoeffBound input j : ℝ) ^ 2))) := hsum_bd
    _ = (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
        ((r : ℝ) * ∑ j ∈ Finset.range n,
          ((Hex.bhksCoeffBound input j : ℝ) ^ 2)) := hsum_factor
    _ = (∑ i : Fin r, ((vec.getD i.val 0 : ℝ) ^ 2)) *
        ((r : ℝ) * (BHKS.cldColumnNormBound input liftData.p : ℝ)) := by rw [hcldcol]

end BHKS

namespace ExecutableBadVectorWitness

/-- Promote an executable `Array Int` row to a vector function indexed by the
witness's projected factor count. -/
def projectedVectorFn (W : ExecutableBadVectorWitness) (vec : Array Int) :
    Fin W.projectedRows.factorCount → ℤ :=
  fun i => vec.getD i.val 0

/-- Store a proof-facing projected vector in the executable array shape used
by the BHKS auxiliary-polynomial construction. -/
def projectedVectorArray (W : ExecutableBadVectorWitness)
    (v : Fin W.projectedRows.factorCount → ℤ) : Array Int :=
  (List.ofFn v).toArray

/--
Canonical executable bad-vector witness for a fixed projected vector.

The auxiliary polynomial field is computed by the same BHKS construction used
in the executable CLD layer, and the selected local-factor degree is read from
the selected lifted factor.  This constructor discharges the structural part of
the BHKS bad-vector setup; the rational coprimality and resultant divisibility
clauses remain the genuine BHKS Lemma 3.2 algebraic obligations.
-/
def ofProjectedVector
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (hrows :
      1 ≤
        (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).factorCount +
          (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).coeffWidth)
    (localFactorIndex : Nat)
    (v :
      Fin (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis input liftData.p liftData.k
          liftData.liftedFactors) hrows).factorCount → ℤ) :
    ExecutableBadVectorWitness where
  input := input
  liftData := liftData
  lattice := Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors
  projectedRows :=
    Hex.bhksProjectedRows
      (Hex.bhksLatticeBasis input liftData.p liftData.k liftData.liftedFactors)
      hrows
  localFactorIndex := localFactorIndex
  localFactorDegree :=
    (liftData.liftedFactors.getD localFactorIndex 0).degree?.getD 0
  H := BHKS.auxiliaryPolynomial input liftData (List.ofFn v).toArray
  lattice_matches_lift := rfl
  projected_factor_count := rfl

/-- `projectedVectorArray` is the canonical array representative of a
proof-facing projected vector. -/
theorem projectedVectorFn_projectedVectorArray
    (W : ExecutableBadVectorWitness)
    (v : Fin W.projectedRows.factorCount → ℤ) :
    W.projectedVectorFn (W.projectedVectorArray v) = v := by
  funext i
  simp [projectedVectorFn, projectedVectorArray]

/-- The executable representative of a projected vector has exactly the
projected factor count as its array size. -/
theorem projectedVectorArray_size
    (W : ExecutableBadVectorWitness)
    (v : Fin W.projectedRows.factorCount → ℤ) :
    (W.projectedVectorArray v).size = W.projectedRows.factorCount := by
  simp [projectedVectorArray]

/-- Reading the executable representative at an in-bounds projected-factor
index recovers the original projected vector entry. -/
theorem projectedVectorArray_getD
    (W : ExecutableBadVectorWitness)
    (v : Fin W.projectedRows.factorCount → ℤ)
    (i : Fin W.projectedRows.factorCount) :
    (W.projectedVectorArray v).getD i.val 0 = v i := by
  simpa [projectedVectorFn] using congrFun (projectedVectorFn_projectedVectorArray W v) i

/--
Bad-vector evidence for an executable BHKS bad-vector witness.

The witness's auxiliary polynomial `H` is the canonical BHKS auxiliary
polynomial of `bhksVector` after subtracting the diagonal correction rows, and
the same vector lies in the projected integer row span `L'` but not in the
true-factor indicator lattice `W`.

This is the proof-facing package of the local BHKS Lemma 3.2 hypotheses used
by the resultant comparison.  Later construction work must prove these fields
from the executable CLD/Hensel data attached to an actual failed recovery run.
-/
structure IsBhksBadVectorSetup (W : ExecutableBadVectorWitness) where
  bhksVector : Array Int
  bhksCorrections : Array Int
  trueSupports : Set (Set (Fin W.projectedRows.factorCount))
  H_eq :
    W.H =
      BHKS.auxiliaryPolynomialWithCorrections
        W.input W.liftData bhksVector bhksCorrections
  in_projected :
    W.projectedVectorFn bhksVector ∈ BHKS.projectedRowSpanInt W.projectedRows
  not_in_indicators :
    W.projectedVectorFn bhksVector ∉
      BHKS.trueFactorIndicatorLattice trueSupports
  localFactorDegree_pos : 0 < W.localFactorDegree
  coprime_input_aux_over_rat :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ))
  resultant_divisible_by_p_pow :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial

/--
Construct the BHKS bad-vector setup from the projected vector shape used by
cap separation.  The structural `L' \ W` fields are transported through the
canonical executable array representation; the local BHKS Lemma 3.2 algebraic
clauses remain explicit hypotheses.
-/
def isBhksBadVectorSetup_of_projected_not_indicator
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (v : Fin W.projectedRows.factorCount → ℤ)
    (corrections : Array Int)
    (hH :
      W.H =
        BHKS.auxiliaryPolynomialWithCorrections W.input W.liftData
          (W.projectedVectorArray v) corrections)
    (hin : v ∈ BHKS.projectedRowSpanInt W.projectedRows)
    (hnot : v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hd : 0 < W.localFactorDegree)
    (hcoprime :
      IsCoprime
        (W.inputPolynomial.map (Int.castRingHom ℚ))
        (W.auxiliaryPolynomial.map (Int.castRingHom ℚ)))
    (hdiv :
      ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
        Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial) :
    IsBhksBadVectorSetup W := by
  refine
    { bhksVector := W.projectedVectorArray v
      bhksCorrections := corrections
      trueSupports := trueSupports
      H_eq := hH
      in_projected := ?_
      not_in_indicators := ?_
      localFactorDegree_pos := hd
      coprime_input_aux_over_rat := hcoprime
      resultant_divisible_by_p_pow := hdiv }
  · simpa [projectedVectorFn_projectedVectorArray] using hin
  · simpa [projectedVectorFn_projectedVectorArray] using hnot

/--
Concrete fixed-vector bad-vector setup constructor.

For a projected vector `v ∈ L' \ W`, the witness built by
`ofProjectedVector` has the canonical auxiliary polynomial by construction and
uses the executable selected local-factor degree.  Callers still provide the
positive-degree fact and the two resultant hypotheses; this is the intended
boundary before the full BHKS Lemma 3.2 proof.
-/
def isBhksBadVectorSetup_of_projectedVector
    (input : Hex.ZPoly) (liftData : Hex.LiftData)
    (hrows :
      1 ≤
        (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).factorCount +
          (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors).coeffWidth)
    (localFactorIndex : Nat)
    (v :
      Fin (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis input liftData.p liftData.k
          liftData.liftedFactors) hrows).factorCount → ℤ)
    (trueSupports :
      Set (Set (Fin (Hex.bhksProjectedRows
        (Hex.bhksLatticeBasis input liftData.p liftData.k
          liftData.liftedFactors) hrows).factorCount)))
    (hin :
      v ∈ BHKS.projectedRowSpanInt
        (Hex.bhksProjectedRows
          (Hex.bhksLatticeBasis input liftData.p liftData.k
            liftData.liftedFactors) hrows))
    (hnot :
      v ∉ BHKS.trueFactorIndicatorLattice trueSupports)
    (hdegree :
      0 < (liftData.liftedFactors.getD localFactorIndex 0).degree?.getD 0)
    (hcoprime :
      IsCoprime
        ((ofProjectedVector input liftData hrows localFactorIndex v).inputPolynomial.map
          (Int.castRingHom ℚ))
        ((ofProjectedVector input liftData hrows localFactorIndex v).auxiliaryPolynomial.map
          (Int.castRingHom ℚ)))
    (hdiv :
      (((ofProjectedVector input liftData hrows localFactorIndex v).liftData.p ^
          ((ofProjectedVector input liftData hrows localFactorIndex v).liftData.k *
            (ofProjectedVector input liftData hrows localFactorIndex v).localFactorDegree) :
          Nat) : ℤ) ∣
        Polynomial.resultant
          (ofProjectedVector input liftData hrows localFactorIndex v).inputPolynomial
          (ofProjectedVector input liftData hrows localFactorIndex v).auxiliaryPolynomial) :
    IsBhksBadVectorSetup
      (ofProjectedVector input liftData hrows localFactorIndex v) := by
  let W := ofProjectedVector input liftData hrows localFactorIndex v
  exact
    isBhksBadVectorSetup_of_projected_not_indicator
      W trueSupports v #[]
      (by
        simp [W, ofProjectedVector, projectedVectorArray, BHKS.auxiliaryPolynomial])
      hin hnot
      (by
        simpa [W, ofProjectedVector] using hdegree)
      hcoprime hdiv

/--
Per-vector algebraic data needed to turn a projected vector in `L' \ W` into
the exact bad-vector setup callback consumed by cap separation.

The structural `L' \ W` facts are supplied by the callback arguments.  This
record packages the remaining BHKS Lemma 3.2 data: the canonical auxiliary
polynomial attached to the projected vector, positivity of the selected local
factor degree, rational coprimality, and the `p^(k*d)` resultant divisibility.

Only `auxiliary_eq` and `auxiliaryCorrections` depend on the projected vector;
the other three fields are properties of the fixed witness data (`W.H`,
`W.input`, `W.liftData`) and are not quantified over `v`.
-/
structure BadVectorBridgeData
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount))) where
  /-- Integer true factors indexed compatibly with the lifted local factors. -/
  trueFactor : Nat → Hex.ZPoly
  /--
  Coefficientwise Hensel-lift congruence between each true factor and the
  corresponding lifted local factor modulo `p^k`.
  -/
  trueFactor_liftedFactor_coeff_dvd :
    ∀ i, i < W.liftData.liftedFactors.size → ∀ j,
      ((W.liftData.p ^ W.liftData.k : Nat) : ℤ) ∣
        (Hex.DensePoly.coeff (trueFactor i) j -
          Hex.DensePoly.coeff (W.liftData.liftedFactors.getD i 0) j)
  /--
  The selected local factor has a true-factor representative satisfying the
  same lift congruence.  This duplicates the selected-index instance in a
  directly reusable form for later local-factor proofs.
  -/
  selected_trueFactor_liftedFactor_coeff_dvd :
    ∀ j,
      ((W.liftData.p ^ W.liftData.k : Nat) : ℤ) ∣
        (Hex.DensePoly.coeff (trueFactor W.localFactorIndex) j -
          Hex.DensePoly.coeff W.selectedLiftedFactor j)
  /--
  Per-coefficient precision separation used by the corrected auxiliary
  polynomial construction.
  -/
  precision_separation :
    ∀ j, j < W.input.degree?.getD 0 →
      2 * Hex.bhksCoeffBound W.input j < W.liftData.p ^ W.liftData.k
  /--
  Diagonal-row correction coordinates for each projected vector in `L' \ W`.
  -/
  projectedCorrections :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ BHKS.projectedRowSpanInt W.projectedRows →
        v ∉ BHKS.trueFactorIndicatorLattice trueSupports →
          Array Int
  /--
  The witness auxiliary polynomial is the corrected BHKS auxiliary polynomial
  for every projected vector in `L' \ W`.

  `badVectorWitnessOfLiftData` keeps `H` as a parameter in `Recovery.lean`, so
  callers instantiate this field with the structural hypothesis identifying
  that parameter with the canonical corrected construction.
  -/
  auxiliary_eq :
    ∀ (v : Fin W.projectedRows.factorCount → ℤ)
      (hin : v ∈ BHKS.projectedRowSpanInt W.projectedRows)
      (hnot : v ∉ BHKS.trueFactorIndicatorLattice trueSupports),
        W.H =
          BHKS.auxiliaryPolynomialWithCorrections W.input W.liftData
            (W.projectedVectorArray v)
            (projectedCorrections v hin hnot)
  localFactorDegree_pos : 0 < W.localFactorDegree
  coprime_input_aux_over_rat :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ))
  resultant_divisible_by_p_pow :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial

namespace BadVectorBridgeData

/-- Correction coordinates supplied by `BadVectorBridgeData`. -/
def auxiliaryCorrections
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports)
    (v : Fin W.projectedRows.factorCount → ℤ)
    (hin : v ∈ BHKS.projectedRowSpanInt W.projectedRows)
    (hnot : v ∉ BHKS.trueFactorIndicatorLattice trueSupports) :
    Array Int :=
  D.projectedCorrections v hin hnot

/--
The corrected auxiliary polynomial identity supplied by
`BadVectorBridgeData`, stated using the public correction accessor.
-/
theorem auxiliary_eq'
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports)
    (v : Fin W.projectedRows.factorCount → ℤ)
    (hin : v ∈ BHKS.projectedRowSpanInt W.projectedRows)
    (hnot : v ∉ BHKS.trueFactorIndicatorLattice trueSupports) :
    W.H =
      BHKS.auxiliaryPolynomialWithCorrections W.input W.liftData
        (W.projectedVectorArray v)
        (D.auxiliaryCorrections v hin hnot) := by
  exact D.auxiliary_eq v hin hnot

/--
Coefficientwise Hensel-lift congruence between every packaged true factor and
the corresponding lifted local factor.
-/
theorem trueFactor_liftedFactor_coeff_dvd_of_bridge_data
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports)
    (i : Nat) (hi : i < W.liftData.liftedFactors.size) (j : Nat) :
    ((W.liftData.p ^ W.liftData.k : Nat) : ℤ) ∣
      (Hex.DensePoly.coeff (D.trueFactor i) j -
        Hex.DensePoly.coeff (W.liftData.liftedFactors.getD i 0) j) := by
  exact D.trueFactor_liftedFactor_coeff_dvd i hi j

/--
Selected-index Hensel-lift congruence supplied by `BadVectorBridgeData`.
-/
theorem selected_trueFactor_liftedFactor_coeff_dvd_of_bridge_data
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports) (j : Nat) :
    ((W.liftData.p ^ W.liftData.k : Nat) : ℤ) ∣
      (Hex.DensePoly.coeff (D.trueFactor W.localFactorIndex) j -
        Hex.DensePoly.coeff W.selectedLiftedFactor j) := by
  exact D.selected_trueFactor_liftedFactor_coeff_dvd j

/--
Per-coefficient precision separation supplied by `BadVectorBridgeData`.
-/
theorem precision_separation_of_bridge_data
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports)
    (j : Nat) (hj : j < W.input.degree?.getD 0) :
    2 * Hex.bhksCoeffBound W.input j < W.liftData.p ^ W.liftData.k := by
  exact D.precision_separation j hj

end BadVectorBridgeData

/--
Compact callback package consumed by cap separation.

`BadVectorBridgeData` is the stronger project-level hypothesis record; its
`toProjectedBadVectorSetupBridge` method forgets the true-factor and precision
fields to this smaller surface.
-/
structure ProjectedBadVectorSetupBridge
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount))) where
  auxiliaryCorrections :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ BHKS.projectedRowSpanInt W.projectedRows →
        v ∉ BHKS.trueFactorIndicatorLattice trueSupports →
          Array Int
  auxiliary_eq :
    ∀ (v : Fin W.projectedRows.factorCount → ℤ)
      (hin : v ∈ BHKS.projectedRowSpanInt W.projectedRows)
      (hnot : v ∉ BHKS.trueFactorIndicatorLattice trueSupports),
          W.H =
            BHKS.auxiliaryPolynomialWithCorrections W.input W.liftData
              (W.projectedVectorArray v)
              (auxiliaryCorrections v hin hnot)
  localFactorDegree_pos : 0 < W.localFactorDegree
  coprime_input_aux_over_rat :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ))
  resultant_divisible_by_p_pow :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial

/--
Forget the project-level bridge data to the compact callback package consumed
by cap separation.
-/
def BadVectorBridgeData.toProjectedBadVectorSetupBridge
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports) :
    ProjectedBadVectorSetupBridge W trueSupports where
  auxiliaryCorrections := D.auxiliaryCorrections
  auxiliary_eq := D.auxiliary_eq'
  localFactorDegree_pos := D.localFactorDegree_pos
  coprime_input_aux_over_rat := D.coprime_input_aux_over_rat
  resultant_divisible_by_p_pow := D.resultant_divisible_by_p_pow

/--
BHKS Lemma 3.2 (selected local-factor degree positivity), exposed from the
project-level bridge package.  Companion accessor to
`coprime_input_aux_over_rat_of_bridge_data` and
`resultant_divisible_by_p_pow_of_bridge_data` used by the bridge assembly
layer.
-/
theorem localFactorDegree_pos_of_bridge_data
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports) :
    0 < W.localFactorDegree := by
  exact D.localFactorDegree_pos

/--
BHKS Lemma 3.2 bridge-data accessor for the rational coprimality clause.

`BadVectorBridgeData` is the executable-witness hypothesis package that carries
the local algebraic content needed by cap separation.  This theorem gives the
named projection used by the bridge assembly layer.
-/
theorem coprime_input_aux_over_rat_of_bridge_data
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports) :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ)) := by
  exact D.coprime_input_aux_over_rat

/--
BHKS Lemma 3.2 (modular divisibility clause), exposed from the project-level
bridge package.
-/
theorem resultant_divisible_by_p_pow_of_bridge_data
    {W : ExecutableBadVectorWitness}
    {trueSupports : Set (Set (Fin W.projectedRows.factorCount))}
    (D : BadVectorBridgeData W trueSupports) :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial := by
  exact D.resultant_divisible_by_p_pow

/--
Convert the packaged `ProjectedBadVectorSetupBridge` into the callback shape
expected by `BHKS.ExecutableCapSeparationHypotheses`.
-/
def bad_setup_of_projected_not_indicator
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    (hbridge : ProjectedBadVectorSetupBridge W trueSupports) :
    ∀ v : Fin W.projectedRows.factorCount → ℤ,
      v ∈ BHKS.projectedRowSpanInt W.projectedRows →
        v ∉ BHKS.trueFactorIndicatorLattice trueSupports →
          IsBhksBadVectorSetup W := by
  intro v hin hnot
  exact
    isBhksBadVectorSetup_of_projected_not_indicator
      W trueSupports v
      (hbridge.auxiliaryCorrections v hin hnot)
      (hbridge.auxiliary_eq v hin hnot)
      hin hnot
      hbridge.localFactorDegree_pos
      hbridge.coprime_input_aux_over_rat
      hbridge.resultant_divisible_by_p_pow

/-- BHKS Lemma 3.2: the selected local-factor degree is positive whenever the
witness carries a bad-vector setup. -/
theorem localFactorDegree_pos_of_bhks_bad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W) :
    0 < W.localFactorDegree := by
  exact h_bad.localFactorDegree_pos

/--
BHKS Lemma 3.2 (rational coprimality clause): the input and auxiliary
polynomials are coprime over `ℚ` whenever the witness carries a bad-vector
setup.
-/
theorem coprime_input_aux_over_rat_of_bhks_bad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W) :
    IsCoprime
      (W.inputPolynomial.map (Int.castRingHom ℚ))
      (W.auxiliaryPolynomial.map (Int.castRingHom ℚ)) := by
  exact h_bad.coprime_input_aux_over_rat

/--
BHKS Lemma 3.2 (modular divisibility clause): the integer resultant of the
input and auxiliary polynomials is divisible by `p^(k * d)` whenever the
witness carries a bad-vector setup, where `p` is the BHKS prime, `k` is the
lift precision, and `d` is the selected local-factor degree.
-/
theorem resultant_divisible_by_p_pow_of_bhks_bad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W) :
    ((W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : Nat) : ℤ) ∣
      Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial := by
  exact h_bad.resultant_divisible_by_p_pow

/--
Package a BHKS bad-vector setup as the abstract resultant data consumed by
the lower/upper-bound comparison lemmas.
-/
def resultantDataOfBhksBad
    (W : ExecutableBadVectorWitness) (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    BadVectorResultantData :=
  W.toResultantData
    hp
    (localFactorDegree_pos_of_bhks_bad W h_bad)
    (coprime_input_aux_over_rat_of_bhks_bad W h_bad)
    (resultant_divisible_by_p_pow_of_bhks_bad W h_bad)

/--
BHKS Lemma 3.2 bound package: a bad-vector setup gives both the modular
resultant lower bound and the Hadamard/l2norm upper bound without callers
projecting the setup fields manually.
-/
theorem badVector_resultant_bounds_of_bhks_bad
    (W : ExecutableBadVectorWitness)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ∧
    |((Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree :=
  W.badVector_resultant_bounds
    hp
    (localFactorDegree_pos_of_bhks_bad W h_bad)
    (coprime_input_aux_over_rat_of_bhks_bad W h_bad)
    (resultant_divisible_by_p_pow_of_bhks_bad W h_bad)

/-- BHKS Lemma 3.2, resultant chain form: the modular divisor lower bound and
the Hadamard upper bound combine to a single real-valued inequality on
`(p ^ (k · d) : ℝ)` and the BHKS l2-norm product, with the integer resultant
absent from the conclusion.

Used by the BHKS Theorem 5.2 separation argument; the auxiliary polynomial's
`l2norm` side is controlled separately by `auxiliaryPolynomial_l2norm_sq_le`. -/
theorem bhks_bad_vector_resultant_lower_bound
    (W : ExecutableBadVectorWitness)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree := by
  exact (W.badVector_resultant_bounds_of_bhks_bad h_bad hp).1.trans
    (W.badVector_resultant_bounds_of_bhks_bad h_bad hp).2

/--
Combined BHKS Lemma 3.2 contradiction: an executable bad-vector witness whose
`H` field is the canonical BHKS auxiliary polynomial of a vector in `L' \ W`
cannot exist once the Hadamard/l2norm upper bound on the integer resultant of
the input and the auxiliary polynomial drops below the modular divisor
`p^(k * d)`.

The selected-degree positivity, rational coprimality, and resultant
divisibility are discharged by `localFactorDegree_pos_of_bhks_bad`,
`coprime_input_aux_over_rat_of_bhks_bad`, and
`resultant_divisible_by_p_pow_of_bhks_bad`; this theorem chains them through
the existing executable bad-vector contradiction
`ExecutableBadVectorWitness.no_badVector_of_l2norm_upper_lt_divisor`.
-/
theorem no_bhks_bad_setup_of_l2norm_upper_lt_divisor
    (W : ExecutableBadVectorWitness)
    (h_bad : IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p)
    (hlt :
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree <
      (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)) :
    False :=
  W.no_badVector_of_l2norm_upper_lt_divisor
    hp
    (localFactorDegree_pos_of_bhks_bad W h_bad)
    (coprime_input_aux_over_rat_of_bhks_bad W h_bad)
    (resultant_divisible_by_p_pow_of_bhks_bad W h_bad)
    hlt

end ExecutableBadVectorWitness

end

end HexBerlekampZassenhausMathlib
