/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyZMathlib.Mignotte
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
Resultant correspondence lemmas for the Berlekamp-Zassenhaus Mathlib layer.

This module packages the upstream resultant API in the integer-polynomial
forms needed by the BHKS bad-vector proof route.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open scoped BigOperators

open Polynomial

/--
Hadamard's determinant bound specialized to integer matrices and Euclidean
row norms.
-/
theorem abs_det_le_row_l2norm_prod
    {N : Nat} (A : Matrix (Fin N) (Fin N) ℤ) :
    |((A.det : ℤ) : ℝ)| ≤
      ∏ i : Fin N, Real.sqrt (∑ j : Fin N, (A i j : ℝ) ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  let o := b.toBasis.orientation
  let rows : Fin N → EuclideanSpace ℝ (Fin N) :=
    fun i => WithLp.toLp 2 (fun j => (A i j : ℝ))
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N) := ⟨by simp⟩
  have hvol : |o.volumeForm rows| ≤ ∏ i : Fin N, ‖rows i‖ :=
    o.abs_volumeForm_apply_le rows
  have hrob : |o.volumeForm rows| = |b.toBasis.det rows| :=
    o.volumeForm_robust' b rows
  have hdet : b.toBasis.det rows = (A.map (Int.castRingHom ℝ)).det := by
    rw [EuclideanSpace.basisFun_toBasis, PiLp.basisFun_eq_pi_basisFun,
      Module.Basis.det_map]
    rw [Pi.basisFun_det_apply]
    rfl
  have hrow (i : Fin N) :
      ‖rows i‖ = Real.sqrt (∑ j : Fin N, (A i j : ℝ) ^ 2) := by
    simp [rows, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  have hdet_cast : (A.map (Int.castRingHom ℝ)).det = ((A.det : ℤ) : ℝ) := by
    exact ((Int.castRingHom ℝ).map_det A).symm
  rw [hrob, hdet, hdet_cast] at hvol
  simpa [hrow] using hvol

/--
Hadamard's bound applied to the Sylvester matrix defining the integer
resultant.
-/
theorem abs_resultant_le_sylvester_row_l2norm_prod
    (f g : Polynomial ℤ) :
    |((Polynomial.resultant f g : ℤ) : ℝ)| ≤
      ∏ i : Fin (f.natDegree + g.natDegree),
        Real.sqrt
          (∑ j : Fin (f.natDegree + g.natDegree),
            (Polynomial.sylvester f g f.natDegree g.natDegree i j : ℝ) ^ 2) := by
  simpa [Polynomial.resultant] using
    abs_det_le_row_l2norm_prod
      (Polynomial.sylvester f g f.natDegree g.natDegree)

/--
Hadamard's determinant bound in column form: bound the determinant by the
product of column Euclidean norms. Obtained from the row form by transposing.
-/
theorem abs_det_le_col_l2norm_prod
    {N : Nat} (A : Matrix (Fin N) (Fin N) ℤ) :
    |((A.det : ℤ) : ℝ)| ≤
      ∏ j : Fin N, Real.sqrt (∑ i : Fin N, (A i j : ℝ) ^ 2) := by
  have h := abs_det_le_row_l2norm_prod A.transpose
  rw [Matrix.det_transpose] at h
  simpa [Matrix.transpose_apply] using h

private lemma pow_card_dvd_prod_of_dvd
    {ι : Type*} [Fintype ι] (m : ℤ) (f : ι → ℤ)
    (h : ∀ i, m ∣ f i) :
    m ^ Fintype.card ι ∣ ∏ i, f i := by
  classical
  rw [Fintype.card]
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd
    (s := Finset.univ) (fun _ : ι => m) f (fun i _ => h i)

/--
If the first `d` columns of an integer matrix are entrywise divisible by `m`,
then `m ^ d` divides the determinant.

The `Fin (d + n)` indexing matches the two natural Sylvester column blocks:
`j.castAdd n` addresses the left block of `d` columns, while the remaining
columns are unconstrained.
-/
theorem det_dvd_of_left_cols_dvd
    {d n : Nat} (m : ℤ) (A : Matrix (Fin (d + n)) (Fin (d + n)) ℤ)
    (hcols : ∀ (j : Fin d) (i : Fin (d + n)), m ∣ A i (j.castAdd n)) :
    m ^ d ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  rw [Fin.prod_univ_add]
  apply dvd_mul_of_dvd_left
  simpa [Fintype.card_fin] using
    (pow_card_dvd_prod_of_dvd m
      (fun j : Fin d => A (σ (j.castAdd n)) (j.castAdd n))
      (fun j => hcols j (σ (j.castAdd n))))

private lemma prod_cols_dvd_prod_univ_of_injective
    {N d : Nat} (f : Fin N → ℤ) (cols : Fin d → Fin N)
    (hcols_inj : Function.Injective cols) :
    (∏ j : Fin d, f (cols j)) ∣ ∏ j : Fin N, f j := by
  classical
  have himage :
      (∏ x ∈ Finset.univ.image cols, f x) =
        ∏ j : Fin d, f (cols j) := by
    rw [Finset.prod_image]
    intro x _ y _ hxy
    exact hcols_inj hxy
  rw [← himage]
  exact Finset.prod_dvd_prod_of_subset (Finset.univ.image cols) Finset.univ f
    (Finset.subset_univ _)

/--
If any specified `d` distinct columns of an integer matrix are entrywise
divisible by `m`, then `m ^ d` divides the determinant.
-/
theorem det_dvd_of_cols_dvd
    {N d : Nat} (m : ℤ) (A : Matrix (Fin N) (Fin N) ℤ)
    (cols : Fin d → Fin N) (hcols_inj : Function.Injective cols)
    (hcols : ∀ (j : Fin d) (i : Fin N), m ∣ A i (cols j)) :
    m ^ d ∣ A.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  have hselected :
      m ^ d ∣ ∏ j : Fin d, A (σ (cols j)) (cols j) := by
    simpa [Fintype.card_fin] using
      (pow_card_dvd_prod_of_dvd m
        (fun j : Fin d => A (σ (cols j)) (cols j))
        (fun j => hcols j (σ (cols j))))
  exact hselected.trans
    (prod_cols_dvd_prod_univ_of_injective
      (fun j : Fin N => A (σ j) j) cols hcols_inj)

/--
Abstract Sylvester-column valuation criterion for integer resultants.

If a determinant-preserving Sylvester column transformation produces `d`
distinct columns whose entries are all divisible by `m`, then `m ^ d` divides
the resultant.  This is the determinant-only core needed by the CLD/logarithmic
derivative argument: downstream code supplies the transformed matrix and column
divisibility witnesses directly, without assuming that the selected local
factor divides the auxiliary polynomial modulo `m`.
-/
theorem dvd_resultant_of_sylvester_cols
    (f H : Polynomial ℤ) {d : Nat} (m : ℤ)
    (A : Matrix (Fin (f.natDegree + H.natDegree)) (Fin (f.natDegree + H.natDegree)) ℤ)
    (cols : Fin d → Fin (f.natDegree + H.natDegree))
    (hcols_inj : Function.Injective cols)
    (hdet : A.det = (Polynomial.sylvester f H f.natDegree H.natDegree).det)
    (hcols : ∀ (j : Fin d) (i : Fin (f.natDegree + H.natDegree)),
      m ∣ A i (cols j)) :
    m ^ d ∣ Polynomial.resultant f H := by
  have hA : m ^ d ∣ A.det := det_dvd_of_cols_dvd m A cols hcols_inj hcols
  rw [hdet] at hA
  simpa [Polynomial.resultant] using hA

/--
Prime-power form of `dvd_resultant_of_sylvester_cols`.

The hypotheses deliberately mention only the Sylvester-column valuation data.
For BHKS/CLD use, the selected monic local factor `q` of degree `d` explains
where the `d` column directions come from, while the actual CLD coefficient
congruences are packaged in `hcols`.  No divisibility hypothesis
`q.map _ ∣ H.map _` is required.
-/
theorem pow_dvd_resultant_of_sylvester_cols
    {p k d : Nat} (f H q : Polynomial ℤ)
    (_hq_monic : q.Monic)
    (_hq_deg : q.natDegree = d)
    (_hf_monic : f.Monic)
    (A : Matrix (Fin (f.natDegree + H.natDegree)) (Fin (f.natDegree + H.natDegree)) ℤ)
    (cols : Fin d → Fin (f.natDegree + H.natDegree))
    (hcols_inj : Function.Injective cols)
    (hdet : A.det = (Polynomial.sylvester f H f.natDegree H.natDegree).det)
    (hcols : ∀ (j : Fin d) (i : Fin (f.natDegree + H.natDegree)),
      ((p ^ k : Nat) : ℤ) ∣ A i (cols j)) :
    ((p ^ (k * d) : Nat) : ℤ) ∣ Polynomial.resultant f H := by
  have hbase :
      ((p ^ k : Nat) : ℤ) ^ d ∣ Polynomial.resultant f H :=
    dvd_resultant_of_sylvester_cols f H ((p ^ k : Nat) : ℤ) A cols hcols_inj hdet hcols
  have hcast : ((p ^ (k * d) : Nat) : ℤ) = ((p ^ k : Nat) : ℤ) ^ d := by
    rw [pow_mul, Nat.cast_pow]
  simpa [hcast]

/--
Replacing a column of a square matrix by `A.mulVec w` — the linear combination
of all columns with coefficients `w` — multiplies the determinant by the
coefficient `w p` of the replaced column.

This is the determinant-preserving column-operation mechanism: when the
replaced column appears in the combination with a *unit* coefficient (`w p = 1`,
the monic-triangular case), the determinant is preserved exactly. It is the
column-form repackaging of `Matrix.det_updateCol_sum` against `mulVec`.
-/
theorem det_updateCol_mulVec
    {R : Type*} [CommRing R] {N : Nat}
    (A : Matrix (Fin N) (Fin N) R) (p : Fin N) (w : Fin N → R) :
    (A.updateCol p (A.mulVec w)).det = w p • A.det := by
  have hcol : A.mulVec w = (fun k => ∑ i, w i • A k i) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hcol, Matrix.det_updateCol_sum]

/-- Squared `l2norm` of an integer polynomial expressed as a sum of squared
coefficients over `Finset.range (natDegree + 1)`, padding with zeros outside
`support`. -/
private lemma l2normSq_eq_sum_range (g : Polynomial ℤ) :
    (HexPolyZMathlib.l2norm g) ^ 2 =
      ∑ k ∈ Finset.range (g.natDegree + 1), ((g.coeff k : ℤ) : ℝ) ^ 2 := by
  unfold HexPolyZMathlib.l2norm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Polynomial.le_natDegree_of_mem_supp x hx
  · intro x _ hx
    have hcoeff : g.coeff x = 0 := by
      by_contra h
      exact hx (Polynomial.mem_support_iff.mpr h)
    rw [hcoeff]
    simp

/-- Helper: a squared sum of an indicator-on-`Set.Icc` over `Fin (m + n)`
collapses to a sum over `Finset.range (n + 1)` after re-indexing. -/
private lemma sum_indicator_Icc_eq_sum_range
    (φ : ℕ → ℝ) (m n : ℕ) (j₁ : ℕ) (hj₁ : j₁ < m) :
    (∑ i : Fin (m + n),
        if (i : ℕ) ∈ Set.Icc j₁ (j₁ + n) then φ ((i : ℕ) - j₁) else 0)
      = ∑ k ∈ Finset.range (n + 1), φ k := by
  simp only [Set.mem_Icc]
  rw [Fin.sum_univ_eq_sum_range
        (fun i => if j₁ ≤ i ∧ i ≤ j₁ + n then φ (i - j₁) else 0) (m + n)]
  rw [← Finset.sum_filter]
  have hfilter :
      ((Finset.range (m + n)).filter (fun i => j₁ ≤ i ∧ i ≤ j₁ + n))
        = Finset.Icc j₁ (j₁ + n) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hx⟩; exact hx
    · rintro hx
      exact ⟨by lia, hx⟩
  rw [hfilter]
  refine Finset.sum_nbij' (fun (i : ℕ) => i - j₁) (fun (k : ℕ) => k + j₁)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range]
    lia
  · intro a ha
    simp only [Finset.mem_range] at ha
    simp only [Finset.mem_Icc]
    exact ⟨by lia, by lia⟩
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    show (a - j₁) + j₁ = a
    lia
  · intro a _
    show (a + j₁) - j₁ = a
    lia
  · intro a _
    rfl

/-- Squared column Euclidean norm of one of the first `m` columns of the
Sylvester matrix `sylvester f g m n` equals the squared `l2norm` of `g`. -/
private lemma sylvester_col_l2normSq_left (f g : Polynomial ℤ)
    (j₁ : Fin f.natDegree) :
    ∑ i : Fin (f.natDegree + g.natDegree),
        ((Polynomial.sylvester f g f.natDegree g.natDegree i
            (j₁.castAdd g.natDegree) : ℤ) : ℝ) ^ 2
      = (HexPolyZMathlib.l2norm g) ^ 2 := by
  -- Reduce the matrix entry via `Fin.addCases_left`.
  have entry_eq : ∀ i : Fin (f.natDegree + g.natDegree),
      ((Polynomial.sylvester f g f.natDegree g.natDegree i
          (j₁.castAdd g.natDegree) : ℤ) : ℝ) ^ 2 =
        if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + g.natDegree)
          then ((g.coeff ((i : ℕ) - (j₁ : ℕ)) : ℤ) : ℝ) ^ 2 else 0 := by
    intro i
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => entry_eq i)]
  rw [sum_indicator_Icc_eq_sum_range
        (fun k => ((g.coeff k : ℤ) : ℝ) ^ 2)
        f.natDegree g.natDegree (j₁ : ℕ) j₁.is_lt]
  exact (l2normSq_eq_sum_range g).symm

/-- Squared column Euclidean norm of one of the last `n` columns of the
Sylvester matrix `sylvester f g m n` equals the squared `l2norm` of `f`. -/
private lemma sylvester_col_l2normSq_right (f g : Polynomial ℤ)
    (j₁ : Fin g.natDegree) :
    ∑ i : Fin (f.natDegree + g.natDegree),
        ((Polynomial.sylvester f g f.natDegree g.natDegree i
            (j₁.natAdd f.natDegree) : ℤ) : ℝ) ^ 2
      = (HexPolyZMathlib.l2norm f) ^ 2 := by
  have entry_eq : ∀ i : Fin (f.natDegree + g.natDegree),
      ((Polynomial.sylvester f g f.natDegree g.natDegree i
          (j₁.natAdd f.natDegree) : ℤ) : ℝ) ^ 2 =
        if (i : ℕ) ∈ Set.Icc (j₁ : ℕ) ((j₁ : ℕ) + f.natDegree)
          then ((f.coeff ((i : ℕ) - (j₁ : ℕ)) : ℤ) : ℝ) ^ 2 else 0 := by
    intro i
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => entry_eq i)]
  -- Swap the summation order: `Fin (m + n)` instead of `Fin (n + m)`.
  rw [show f.natDegree + g.natDegree = g.natDegree + f.natDegree from
        Nat.add_comm _ _]
  rw [sum_indicator_Icc_eq_sum_range
        (fun k => ((f.coeff k : ℤ) : ℝ) ^ 2)
        g.natDegree f.natDegree (j₁ : ℕ) j₁.is_lt]
  exact (l2normSq_eq_sum_range f).symm

/-- Mignotte-style coefficient bound on the integer resultant of two
polynomials: bound the absolute value of `Polynomial.resultant f g` by the
product of the polynomial coefficient `l2norm`s, with the standard exponents
appearing in BHKS. -/
theorem abs_resultant_le_l2norm_pow (f g : Polynomial ℤ) :
    |((Polynomial.resultant f g : ℤ) : ℝ)| ≤
      (HexPolyZMathlib.l2norm f) ^ g.natDegree *
        (HexPolyZMathlib.l2norm g) ^ f.natDegree := by
  set m := f.natDegree
  set n := g.natDegree
  -- Hadamard's bound applied to the columns of the Sylvester matrix.
  have hcol :=
    abs_det_le_col_l2norm_prod (Polynomial.sylvester f g m n)
  -- Identify the determinant of the Sylvester matrix with the resultant.
  rw [show (Polynomial.sylvester f g m n).det = Polynomial.resultant f g from rfl]
    at hcol
  -- Split the column product into the first `m` columns (g-shifts)
  -- and the last `n` columns (f-shifts).
  rw [Fin.prod_univ_add] at hcol
  -- Identify each block of column norms.
  have hleft :
      (∏ j₁ : Fin m,
          Real.sqrt
            (∑ i : Fin (m + n),
              ((Polynomial.sylvester f g m n i (j₁.castAdd n) : ℤ) : ℝ) ^ 2))
        = (HexPolyZMathlib.l2norm g) ^ m := by
    have hg_nonneg : 0 ≤ HexPolyZMathlib.l2norm g := by
      unfold HexPolyZMathlib.l2norm; exact Real.sqrt_nonneg _
    rw [Finset.prod_congr rfl
      (fun j₁ _ => by
        rw [sylvester_col_l2normSq_left f g j₁,
            Real.sqrt_sq hg_nonneg])]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hright :
      (∏ j₁ : Fin n,
          Real.sqrt
            (∑ i : Fin (m + n),
              ((Polynomial.sylvester f g m n i (j₁.natAdd m) : ℤ) : ℝ) ^ 2))
        = (HexPolyZMathlib.l2norm f) ^ n := by
    have hf_nonneg : 0 ≤ HexPolyZMathlib.l2norm f := by
      unfold HexPolyZMathlib.l2norm; exact Real.sqrt_nonneg _
    rw [Finset.prod_congr rfl
      (fun j₁ _ => by
        rw [sylvester_col_l2normSq_right f g j₁,
            Real.sqrt_sq hf_nonneg])]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hleft, hright] at hcol
  -- Re-arrange the product to match the BHKS-shaped goal.
  linarith [hcol, mul_comm ((HexPolyZMathlib.l2norm g) ^ m)
              ((HexPolyZMathlib.l2norm f) ^ n)]

/--
The upstream resultant nonvanishing theorem specialized to integer
polynomials.
-/
theorem int_resultant_ne_zero_of_coprime
    (f g : Polynomial ℤ) (h : IsCoprime f g) :
    Polynomial.resultant f g ≠ 0 :=
  Polynomial.resultant_ne_zero f g h

/--
Mapping an integer resultant to `ℚ` agrees with taking the resultant after
mapping both input polynomials to `ℚ`.
-/
theorem resultant_map_intCast_rat
    (f g : Polynomial ℤ) :
    Polynomial.resultant (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) =
      ((@Polynomial.resultant ℤ _ f g f.natDegree g.natDegree) : ℚ) := by
  rw [Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom ℚ)) f,
      Polynomial.natDegree_map_eq_of_injective
        (RingHom.injective_int (Int.castRingHom ℚ)) g]
  exact Polynomial.resultant_map_map f g f.natDegree g.natDegree
    (Int.castRingHom ℚ)

/--
The integer resultant vanishes exactly when the rationally transported
polynomials are nontrivially non-coprime.
-/
theorem int_resultant_eq_zero_iff_not_coprime_over_rat
    (f g : Polynomial ℤ) :
    Polynomial.resultant f g = 0 ↔
      ((f.map (Int.castRingHom ℚ) ≠ 0 ∨ g.map (Int.castRingHom ℚ) ≠ 0) ∧
        ¬ IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) := by
  constructor
  · intro hres
    have hresQ :
        Polynomial.resultant (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) = 0 := by
      rw [resultant_map_intCast_rat]
      exact_mod_cast hres
    exact (Polynomial.resultant_eq_zero_iff).mp hresQ
  · intro h
    have hresQ :
        Polynomial.resultant (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) = 0 :=
      (Polynomial.resultant_eq_zero_iff).mpr h
    have hcast : ((@Polynomial.resultant ℤ _ f g f.natDegree g.natDegree) : ℚ) = 0 := by
      rw [← resultant_map_intCast_rat]
      exact hresQ
    exact_mod_cast hcast

/--
Contrapositive form useful when the BHKS route proves coprimality after
transporting an integer-polynomial pair to `ℚ`.
-/
theorem int_resultant_ne_zero_of_coprime_over_rat
    (f g : Polynomial ℤ)
    (hcoprime : IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ))) :
    Polynomial.resultant f g ≠ 0 := by
  intro hres
  have h :=
    (int_resultant_eq_zero_iff_not_coprime_over_rat f g).mp hres
  exact h.2 hcoprime

/--
Integer witnesses from a `ZMod n` divisibility of mapped integer polynomials.
If `q` divides `f` after reducing both modulo `n`, then there are honest integer
polynomial witnesses `a, r` with `f = q * a + C n * r`. No monicity hypothesis is
needed: surjectivity of `ℤ → ZMod n` lifts the modular quotient, and the residual
`f - q * a` is coefficientwise divisible by `n`.
-/
theorem exists_witnesses_of_map_dvd_zmod
    {f q : Polynomial ℤ} {n : ℕ}
    (hdvd : q.map (Int.castRingHom (ZMod n)) ∣
            f.map (Int.castRingHom (ZMod n))) :
    ∃ a r : Polynomial ℤ, f = q * a + Polynomial.C (n : ℤ) * r := by
  obtain ⟨b, hb⟩ := hdvd
  -- Lift the `ZMod n` quotient `b` to an integer polynomial `a`.
  have hsurj : Function.Surjective (Polynomial.map (Int.castRingHom (ZMod n))) :=
    Polynomial.map_surjective _ ZMod.intCast_surjective
  obtain ⟨a, ha⟩ := hsurj b
  -- `f - q * a` reduces to zero mod `n`.
  have hzero : (f - q * a).map (Int.castRingHom (ZMod n)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, ha, ← hb, sub_self]
  -- Hence each coefficient is divisible by `n`, so `C n` divides `f - q * a`.
  have hCdvd : Polynomial.C (n : ℤ) ∣ (f - q * a) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro k
    have hc : ((f - q * a).coeff k : ZMod n) = 0 := by
      have h0 : ((f - q * a).map (Int.castRingHom (ZMod n))).coeff k = 0 := by
        rw [hzero]; simp
      rwa [Polynomial.coeff_map] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hc
  obtain ⟨r, hr⟩ := hCdvd
  exact ⟨a, r, by rw [← hr]; ring⟩

/-- A shifted polynomial belongs to `degreeLT` when its natural degree is
strictly below the bound. -/
theorem mul_X_pow_mem_degreeLT_of_natDegree_lt
    {R : Type*} [Semiring R] (p : Polynomial R) {m t : Nat}
    (hdeg : (p * Polynomial.X ^ t).natDegree < m) :
    p * Polynomial.X ^ t ∈ Polynomial.degreeLT R m := by
  by_cases hp : p * Polynomial.X ^ t = 0
  · rw [hp]
    exact Submodule.zero_mem _
  · exact Polynomial.mem_degreeLT.mpr
      ((Polynomial.natDegree_lt_iff_degree_lt hp).mp hdeg)

/-- Negated shifted-polynomial version of
`mul_X_pow_mem_degreeLT_of_natDegree_lt`, used by the left component of the
common-factor Sylvester syzygy. -/
theorem neg_mul_X_pow_mem_degreeLT_of_natDegree_lt
    {R : Type*} [CommRing R] (p : Polynomial R) {m t : Nat}
    (hdeg : (p * Polynomial.X ^ t).natDegree < m) :
    -p * Polynomial.X ^ t ∈ Polynomial.degreeLT R m := by
  rw [neg_mul]
  by_cases hp : p * Polynomial.X ^ t = 0
  · rw [hp, neg_zero]
    exact Submodule.zero_mem _
  · exact Polynomial.mem_degreeLT.mpr
      ((Polynomial.natDegree_lt_iff_degree_lt (by simp [hp])).mp
        (by simpa [Polynomial.natDegree_neg] using hdeg))

/--
Common-factor syzygy for the Sylvester map.

If `f = q * a` and `g = q * b`, then the shifted pair
`(-a * X^t, b * X^t)` is killed by the Sylvester map for `(f, g)`.  Later
column-reduction work uses the `q.natDegree` shifts of this identity after
reducing explicit quotient/remainder witnesses modulo `m`.
-/
theorem sylvesterMap_commonFactor_syzygy
    {R : Type*} [CommRing R]
    (q a b : Polynomial R) {m n t : Nat}
    (hleft : -a * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hright : b * Polynomial.X ^ t ∈ Polynomial.degreeLT R n)
    (hf : (q * a).natDegree ≤ m)
    (hg : (q * b).natDegree ≤ n) :
    Polynomial.sylvesterMap (q * a) (q * b) hf hg
      (⟨-a * Polynomial.X ^ t, hleft⟩,
       ⟨b * Polynomial.X ^ t, hright⟩) = 0 := by
  ext1
  dsimp [Polynomial.sylvesterMap]
  ring_nf

/--
Scalar-shifted common-factor syzygy for the Sylvester map.

When `f` and `g` share the factor `q` only after reducing modulo a scalar `c`
— recorded by the explicit witnesses `f = q * a + C c * r` and
`g = q * b + C c * s` — the shifted pair `(-a * X^t, b * X^t)` is no longer
killed by the Sylvester map, but its image is the *scalar multiple*
`C c * ((r * b - s * a) * X^t)`.

This is the bridge from the exact syzygy `sylvesterMap_commonFactor_syzygy`
(the `c = 0` case) to the divisibility used by the column-reduction proof: the
linear combination of Sylvester columns selected by `(-a * X^t, b * X^t)` is
entrywise divisible by `c`. Taking `t < q.natDegree` shifts gives `d`
independent such combinations.
-/
theorem sylvesterMap_commonFactor_smul
    {R : Type*} [CommRing R]
    (q a b r s : Polynomial R) (c : R) {m n t : Nat}
    (hleft : -a * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hright : b * Polynomial.X ^ t ∈ Polynomial.degreeLT R n)
    (hf : (q * a + Polynomial.C c * r).natDegree ≤ m)
    (hg : (q * b + Polynomial.C c * s).natDegree ≤ n) :
    (Polynomial.sylvesterMap (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) hf hg
      (⟨-a * Polynomial.X ^ t, hleft⟩,
       ⟨b * Polynomial.X ^ t, hright⟩) : Polynomial R)
      = Polynomial.C c * ((r * b - s * a) * Polynomial.X ^ t) := by
  dsimp [Polynomial.sylvesterMap]
  ring

/--
Each entry of the Sylvester column combination selected by the shifted
common-factor direction `(-a * X^t, b * X^t)` is the scalar `c` times a fixed
coefficient.

The coordinate vector of the direction in the product basis multiplies the
Sylvester matrix to the coordinate vector of the image
`C c * ((r * b - s * a) * X^t)` (`sylvesterMap_commonFactor_smul`), whose
coefficients are visibly `c`-multiples. Hence the selected column combination
is entrywise divisible by `c`: this is the per-entry input the determinant
column-reduction needs once the `q.natDegree` shifts are assembled.
-/
theorem sylvester_mulVec_commonFactor_smul
    {R : Type*} [CommRing R]
    (q a b r s : Polynomial R) (c : R) {m n t : Nat}
    (hleft : -a * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hright : b * Polynomial.X ^ t ∈ Polynomial.degreeLT R n)
    (hf : (q * a + Polynomial.C c * r).natDegree ≤ m)
    (hg : (q * b + Polynomial.C c * s).natDegree ≤ n)
    (i : Fin (m + n)) :
    (Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n).mulVec
        ((Polynomial.degreeLT.basisProd R m n).repr
          (⟨-a * Polynomial.X ^ t, hleft⟩, ⟨b * Polynomial.X ^ t, hright⟩)) i
      = c * ((r * b - s * a) * Polynomial.X ^ t).coeff i := by
  have hmat := (Polynomial.toMatrix_sylvesterMap' (q * a + Polynomial.C c * r)
    (q * b + Polynomial.C c * s) hf hg).symm
  rw [Polynomial.degreeLT.basisProd] at *
  rw [hmat, LinearMap.toMatrix_mulVec_repr]
  rw [Polynomial.degreeLT.basis_repr, sylvesterMap_commonFactor_smul,
    Polynomial.coeff_C_mul]

/--
The monic-triangular column-reduction step for the Sylvester matrix.

Write `w` for the coordinate vector of the shifted common-factor direction
`(-a * X^t, b * X^t)`. Replacing column `p` of the Sylvester matrix `S` by the
combination `S.mulVec w` (the syzygy column):

- multiplies the determinant by the pivot coefficient `w p`
  (`det_updateCol_mulVec`); in the monic-triangular case `w p = 1` this is a
  determinant-*preserving* operation, and
- produces a column whose every entry is divisible by the scalar `c`
  (`sylvester_mulVec_commonFactor_smul`).

Assembling this step over the `d = q.natDegree` shifts `t < d`, with the pivots
chosen so each `w p = 1`, gives the matrix `A'` of the column-reduction target:
`A'.det = S.det` with `d` columns entrywise divisible by `c`. The remaining work
is the bookkeeping that the chosen pivots carry unit coefficients (a leading
coefficient of the cofactor, hence `1` under the monic hypothesis) and that the
combinations reference only as-yet-unreplaced columns.
-/
theorem sylvester_commonFactor_colReduceStep
    {R : Type*} [CommRing R]
    (q a b r s : Polynomial R) (c : R) {m n t : Nat}
    (hleft : -a * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hright : b * Polynomial.X ^ t ∈ Polynomial.degreeLT R n)
    (hf : (q * a + Polynomial.C c * r).natDegree ≤ m)
    (hg : (q * b + Polynomial.C c * s).natDegree ≤ n)
    (p : Fin (m + n)) :
    let S := Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n
    let w := (Polynomial.degreeLT.basisProd R m n).repr
      (⟨-a * Polynomial.X ^ t, hleft⟩, ⟨b * Polynomial.X ^ t, hright⟩)
    (S.updateCol p (S.mulVec w)).det = w p • S.det ∧
      ∀ k, c ∣ (S.mulVec w) k := by
  refine ⟨det_updateCol_mulVec _ p _, fun k => ?_⟩
  rw [sylvester_mulVec_commonFactor_smul q a b r s c hleft hright hf hg k]
  exact Dvd.intro _ rfl

/--
General Sylvester column-image identity.

The Sylvester matrix applied (`mulVec`) to the coordinate vector of a direction
`(u, w)` in the product basis reads off, entry by entry, the coefficients of the
image polynomial `f * w + g * u` under the Sylvester map.  This is the
direction-agnostic core behind the common-factor specialisation
`sylvester_mulVec_commonFactor_smul`: divisibility of a selected column
combination reduces to divisibility of the coefficients of `f * w + g * u`.
-/
theorem sylvester_mulVec_image
    {R : Type*} [CommRing R] (f g u w : Polynomial R) {m n : Nat}
    (hu : u ∈ Polynomial.degreeLT R m) (hw : w ∈ Polynomial.degreeLT R n)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (i : Fin (m + n)) :
    (Polynomial.sylvester f g m n).mulVec
        ((Polynomial.degreeLT.basisProd R m n).repr (⟨u, hu⟩, ⟨w, hw⟩)) i
      = (f * w + g * u).coeff i := by
  have hmat := (Polynomial.toMatrix_sylvesterMap' f g hf hg).symm
  rw [Polynomial.degreeLT.basisProd] at *
  rw [hmat, LinearMap.toMatrix_mulVec_repr, Polynomial.degreeLT.basis_repr]
  rfl

/--
Each entry of the Sylvester column combination selected by the CLD syzygy
direction `(q * X^t, -q' * X^t)` is divisible by the scalar `c`.

The CLD syzygy hypothesis records that the monic selected factor `q` of `f`
satisfies `g * q - f * q' = C c * z` — for the BHKS application `c = p ^ k`, `f`
the input polynomial, `g` the auxiliary polynomial, and the congruence supplied
by `cldQuotientMod_congr_mul_derivative` (rearranged so the divisor `q` does not
have to divide the auxiliary polynomial `g`).  The selected column combination is
the coordinate image of `(q * X^t, -q' * X^t)`, whose Sylvester image is
`(g * q - f * q') * X^t = C c * (z * X^t)` — visibly a `c`-multiple entrywise.
This is the per-entry input the determinant column-reduction needs once the
`d = q.natDegree` shifts `t < d` are assembled into the `d` selected columns.
-/
theorem sylvester_mulVec_cld_syzygy
    {R : Type*} [CommRing R] (f g q z : Polynomial R) (c : R) {m n t : Nat}
    (hsyz : g * q - f * Polynomial.derivative q = Polynomial.C c * z)
    (hu : q * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hw : -Polynomial.derivative q * Polynomial.X ^ t ∈ Polynomial.degreeLT R n)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (i : Fin (m + n)) :
    c ∣ (Polynomial.sylvester f g m n).mulVec
        ((Polynomial.degreeLT.basisProd R m n).repr
          (⟨q * Polynomial.X ^ t, hu⟩,
           ⟨-Polynomial.derivative q * Polynomial.X ^ t, hw⟩)) i := by
  rw [sylvester_mulVec_image f g _ _ hu hw hf hg i]
  have himg : f * (-Polynomial.derivative q * Polynomial.X ^ t)
      + g * (q * Polynomial.X ^ t)
      = Polynomial.C c * (z * Polynomial.X ^ t) := by
    have hrw : f * (-Polynomial.derivative q * Polynomial.X ^ t)
        + g * (q * Polynomial.X ^ t)
        = (g * q - f * Polynomial.derivative q) * Polynomial.X ^ t := by ring
    rw [hrw, hsyz]; ring
  rw [himg, Polynomial.coeff_C_mul]
  exact dvd_mul_right c _

/-- Value of `degreeLT.basisProd`'s coordinate functional on a left-block index:
the coordinate at `i₁.castAdd n` reads off the `i₁`-th coefficient of the first
component. -/
theorem basisProd_repr_castAdd {R : Type*} [CommRing R] {m n : Nat}
    (p : Polynomial.degreeLT R m) (w : Polynomial.degreeLT R n) (i₁ : Fin m) :
    (Polynomial.degreeLT.basisProd R m n).repr (p, w) (i₁.castAdd n)
      = (p : Polynomial R).coeff i₁ := by
  rw [Polynomial.degreeLT.basisProd, Module.Basis.repr_reindex_apply,
    finSumFinEquiv_symm_apply_castAdd, Module.Basis.prod_repr_inl,
    Polynomial.degreeLT.basis_repr]

/-- Value of `degreeLT.basisProd`'s coordinate functional on a right-block index:
the coordinate at `i₂.natAdd m` reads off the `i₂`-th coefficient of the second
component. -/
theorem basisProd_repr_natAdd {R : Type*} [CommRing R] {m n : Nat}
    (p : Polynomial.degreeLT R m) (w : Polynomial.degreeLT R n) (i₂ : Fin n) :
    (Polynomial.degreeLT.basisProd R m n).repr (p, w) (i₂.natAdd m)
      = (w : Polynomial R).coeff i₂ := by
  rw [Polynomial.degreeLT.basisProd, Module.Basis.repr_reindex_apply,
    finSumFinEquiv_symm_apply_natAdd, Module.Basis.prod_repr_inr,
    Polynomial.degreeLT.basis_repr]

/-- A `Fin n` product of a step function `1 ↦ … ↦ 1, C ↦ … ↦ C` that switches to
`C` exactly on the top `d` indices evaluates to `C ^ d`. -/
private lemma prod_threshold {R : Type*} [CommRing R] (C : R) {n d : Nat}
    (hd : d ≤ n) :
    ∏ i : Fin n, (if n - d ≤ (i : ℕ) then C else 1) = C ^ d := by
  have hn : (n - d) + d = n := Nat.sub_add_cancel hd
  rw [← Fin.prod_congr' (fun i : Fin n => if n - d ≤ (i : ℕ) then C else (1 : R)) hn,
    Fin.prod_univ_add]
  have h1 : (∏ i : Fin (n - d),
      (fun x : Fin ((n - d) + d) => if n - d ≤ ((Fin.cast hn x : Fin n) : ℕ) then C else (1 : R))
        (Fin.castAdd d i)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have := i.is_lt
    simp only [Fin.coe_cast, Fin.coe_castAdd]
    exact if_neg (by omega)
  have h2 : (∏ i : Fin d,
      (fun x : Fin ((n - d) + d) => if n - d ≤ ((Fin.cast hn x : Fin n) : ℕ) then C else (1 : R))
        (Fin.natAdd (n - d) i)) = C ^ d := by
    rw [Finset.prod_congr rfl (fun i _ => by
      simp only [Fin.coe_cast, Fin.coe_natAdd]; exact if_pos (by omega))]
    exact Fin.prod_const d C
  rw [h1, h2, one_mul]

/--
The column-reduction transformation matrix for the common-factor Sylvester
reduction.

In the natural `Fin (m + n)` Sylvester column layout, columns `m + (n - d) ..
m + n - 1` (the top `d` columns of the `f`-shift block) are the *pivot* columns.
This matrix is the identity except on those `d` pivot columns, where column
`m + (n - d) + t` carries the coordinate vector of the shifted common-factor
direction `(-a * X^t, b * X^t)` — its left `m` entries are the coefficients of
`-a * X^t`, its right `n` entries those of `b * X^t`.

Multiplying the Sylvester matrix `S` on the right by this matrix replaces each
pivot column by the syzygy combination `S.mulVec (direction)` while leaving the
others fixed. The matrix is upper triangular with diagonal entry `b.coeff (n-d)`
at each pivot (and `1` elsewhere), so `det = (b.coeff (n-d)) ^ d`; under a monic
cofactor `b` this diagonal entry is `1` and the determinant is preserved.
-/
def colReduceTransform {R : Type*} [CommRing R] (a b : Polynomial R) (m n d : Nat) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  Matrix.of fun i j =>
    j.addCases
      (fun _j₁ => if i = j then 1 else 0)
      (fun j₂ =>
        if n - d ≤ (j₂ : ℕ) then
          i.addCases
            (fun i₁ => (-a * Polynomial.X ^ ((j₂ : ℕ) - (n - d))).coeff i₁)
            (fun i₂ => (b * Polynomial.X ^ ((j₂ : ℕ) - (n - d))).coeff i₂)
        else if i = j then 1 else 0)

/-- `colReduceTransform` is upper triangular: below-diagonal entries vanish. The
pivot columns are supported on rows `≤` the pivot because `-a * X^t` lives in
`degreeLT m` (left block, all rows `< m ≤` pivot) and `b * X^t` has degree
`≤ (n - d) + t` (right block, capped at the pivot row), using `b.natDegree ≤ n - d`. -/
theorem colReduceTransform_blockTriangular {R : Type*} [CommRing R] (a b : Polynomial R)
    {m n d : Nat} (hd : d ≤ n) (hb : b.natDegree + d ≤ n) :
    (colReduceTransform a b m n d).BlockTriangular id := by
  intro i j hlt
  simp only [id_eq, Fin.lt_def] at hlt
  rw [colReduceTransform, Matrix.of_apply]
  induction j using Fin.addCases with
  | left j₁ =>
      simp only [Fin.addCases_left]
      exact if_neg (fun h => by simp [h] at hlt)
  | right j₂ =>
      simp only [Fin.addCases_right, Fin.coe_natAdd] at hlt ⊢
      by_cases hpiv : n - d ≤ (j₂ : ℕ)
      · simp only [hpiv, if_true]
        induction i using Fin.addCases with
        | left i₁ =>
            simp only [Fin.coe_castAdd] at hlt
            have := i₁.is_lt
            omega
        | right i₂ =>
            simp only [Fin.addCases_right, Fin.coe_natAdd] at hlt ⊢
            rw [Polynomial.coeff_mul_X_pow']
            have hbz : b.natDegree < (i₂ : ℕ) - ((j₂ : ℕ) - (n - d)) := by omega
            split_ifs with h
            · exact Polynomial.coeff_eq_zero_of_natDegree_lt hbz
            · rfl
      · simp only [hpiv, if_false]
        exact if_neg (fun h => by simp [h, Fin.lt_def] at hlt)

/-- The determinant of `colReduceTransform` is `(b.coeff (n - d)) ^ d`. -/
theorem colReduceTransform_det {R : Type*} [CommRing R] (a b : Polynomial R)
    {m n d : Nat} (hd : d ≤ n) (hb : b.natDegree + d ≤ n) :
    (colReduceTransform a b m n d).det = (b.coeff (n - d)) ^ d := by
  rw [Matrix.det_of_upperTriangular (colReduceTransform_blockTriangular a b hd hb),
    Fin.prod_univ_add]
  have hleft : (∏ i₁ : Fin m,
      colReduceTransform a b m n d (i₁.castAdd n) (i₁.castAdd n)) = 1 := by
    apply Finset.prod_eq_one
    intro i₁ _
    simp [colReduceTransform]
  have hright : (∏ i₂ : Fin n,
      colReduceTransform a b m n d (i₂.natAdd m) (i₂.natAdd m))
        = ∏ i₂ : Fin n, (if n - d ≤ (i₂ : ℕ) then b.coeff (n - d) else 1) := by
    apply Finset.prod_congr rfl
    intro i₂ _
    rw [colReduceTransform, Matrix.of_apply, Fin.addCases_right]
    by_cases hpiv : n - d ≤ (i₂ : ℕ)
    · simp only [hpiv, if_true, Fin.addCases_right]
      rw [Polynomial.coeff_mul_X_pow', if_pos (by omega)]
      congr 1
      omega
    · simp [hpiv]
  rw [hleft, hright, one_mul, prod_threshold _ hd]

/-- The pivot column `m + (n - d) + t` of `colReduceTransform` is the coordinate
vector of the shifted common-factor direction `(-a * X^t, b * X^t)` in
`degreeLT.basisProd`. -/
theorem colReduceTransform_pivot_col {R : Type*} [CommRing R] (a b : Polynomial R)
    {m n d : Nat} (t : Nat) (htd : t < d) (hdn : d ≤ n)
    (hl : -a * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hr : b * Polynomial.X ^ t ∈ Polynomial.degreeLT R n) :
    (fun k => colReduceTransform a b m n d k ((⟨n - d + t, by omega⟩ : Fin n).natAdd m))
      = (Polynomial.degreeLT.basisProd R m n).repr
          (⟨-a * Polynomial.X ^ t, hl⟩, ⟨b * Polynomial.X ^ t, hr⟩) := by
  funext k
  rw [colReduceTransform, Matrix.of_apply, Fin.addCases_right]
  simp only [Fin.coe_natAdd]
  rw [if_pos (by omega)]
  have hexp : n - d + t - (n - d) = t := by omega
  rw [hexp]
  induction k using Fin.addCases with
  | left k₁ => rw [Fin.addCases_left, basisProd_repr_castAdd]
  | right k₂ => rw [Fin.addCases_right, basisProd_repr_natAdd]

set_option maxHeartbeats 400000 in
/--
Assembled common-factor column reduction for the Sylvester matrix.

Write `S = sylvester (q*a + C c*r) (q*b + C c*s) m n` for the Sylvester matrix of
two polynomials sharing the factor `q` modulo the scalar `c` (recorded by the
explicit witnesses `f = q*a + C c*r`, `g = q*b + C c*s`). Right-multiplying `S` by
`colReduceTransform a b m n d` produces a matrix `A'` whose

- determinant is `(b.coeff (n - d)) ^ d * S.det` — the cofactor leading
  coefficient raised to the `d = q.natDegree` shifts; under a *monic* cofactor
  `b` (so `b.coeff (n - d) = 1`) this is exactly `S.det`, and

- top `d` `f`-shift columns (the pivots `m + (n - d) + t` for `t : Fin d`) are
  entrywise divisible by `c`.

This is the matrix `A'` that #6858 feeds to `det_dvd_of_left_cols_dvd` (after a
column reindex moving the `d` divisible columns to the front) to obtain
`c ^ d ∣ S.det = ± resultant`. The degree side conditions `a.natDegree + d ≤ m`,
`b.natDegree + d ≤ n` are the natural cofactor-degree bounds (`deg a = m - d`,
`deg b = n - d`); `hf`, `hg` bound the witnessed polynomials.
-/
theorem sylvester_commonFactor_colReduce {R : Type*} [CommRing R]
    (q a b r s : Polynomial R) (c : R) {m n d : Nat}
    (hd : d ≤ n)
    (ha : a.natDegree + d ≤ m)
    (hb : b.natDegree + d ≤ n)
    (hf : (q * a + Polynomial.C c * r).natDegree ≤ m)
    (hg : (q * b + Polynomial.C c * s).natDegree ≤ n) :
    (Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n
        * colReduceTransform a b m n d).det
      = (b.coeff (n - d)) ^ d
        * (Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n).det
      ∧ ∀ (t : Fin d) (i : Fin (m + n)),
        c ∣ (Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n
            * colReduceTransform a b m n d) i
          ((⟨n - d + (t : ℕ), by have := t.is_lt; omega⟩ : Fin n).natAdd m) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_mul, colReduceTransform_det a b hd hb, mul_comm]
  · intro t i
    have ht := t.is_lt
    -- membership witnesses for the shifted direction, from the cofactor degree bounds
    have hl : -a * Polynomial.X ^ (t : ℕ) ∈ Polynomial.degreeLT R m := by
      apply neg_mul_X_pow_mem_degreeLT_of_natDegree_lt
      have h1 : (a * Polynomial.X ^ (t : ℕ)).natDegree ≤ a.natDegree + (t : ℕ) :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add_left (Polynomial.natDegree_X_pow_le (t : ℕ)) _)
      have h2 : a.natDegree + (t : ℕ) < m := by omega
      exact lt_of_le_of_lt h1 h2
    have hr : b * Polynomial.X ^ (t : ℕ) ∈ Polynomial.degreeLT R n := by
      apply mul_X_pow_mem_degreeLT_of_natDegree_lt
      have h1 : (b * Polynomial.X ^ (t : ℕ)).natDegree ≤ b.natDegree + (t : ℕ) :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add_left (Polynomial.natDegree_X_pow_le (t : ℕ)) _)
      have h2 : b.natDegree + (t : ℕ) < n := by omega
      exact lt_of_le_of_lt h1 h2
    -- the pivot column is the direction's coordinate vector; expand as a mulVec
    rw [show (Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n
        * colReduceTransform a b m n d) i
        ((⟨n - d + (t : ℕ), by omega⟩ : Fin n).natAdd m)
          = (Polynomial.sylvester (q * a + Polynomial.C c * r) (q * b + Polynomial.C c * s) m n).mulVec
              ((Polynomial.degreeLT.basisProd R m n).repr
                (⟨-a * Polynomial.X ^ (t : ℕ), hl⟩, ⟨b * Polynomial.X ^ (t : ℕ), hr⟩)) i from by
      rw [← colReduceTransform_pivot_col a b (t : ℕ) ht hd hl hr]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]]
    rw [sylvester_mulVec_commonFactor_smul q a b r s c hl hr hf hg i]
    exact Dvd.intro _ rfl

/--
Explicit-witness common-factor divisibility for integer resultants.

If `f` and `g` share a monic degree-`d` factor `q` modulo `m`, recorded by
integer witnesses `f = q*a + C m*r` and `g = q*b + C m*s`, and the cofactor
`b` supplies the monic pivot used by the Sylvester column reduction, then
`m ^ d` divides the integer resultant of `f` and `g`.
-/
theorem commonFactor_dvd_resultant
    (f g q a b r s : Polynomial ℤ) (m : ℤ) {d : Nat}
    (hf_wit : f = q * a + Polynomial.C m * r)
    (hg_wit : g = q * b + Polynomial.C m * s)
    (hq_monic : q.Monic)
    (hq_deg : q.natDegree = d)
    (hd : d ≤ g.natDegree)
    (ha : a.natDegree + d ≤ f.natDegree)
    (hb : b.natDegree + d ≤ g.natDegree)
    (hb_pivot : b.coeff (g.natDegree - d) = 1) :
    m ^ d ∣ Polynomial.resultant f g := by
  classical
  have hq_monic_used : q.Monic := hq_monic
  have hq_deg_used : q.natDegree = d := hq_deg
  subst f
  subst g
  let f0 := q * a + Polynomial.C m * r
  let g0 := q * b + Polynomial.C m * s
  let S := Polynomial.sylvester f0 g0 f0.natDegree g0.natDegree
  let T := colReduceTransform a b f0.natDegree g0.natDegree d
  let A := S * T
  have hf_bound : (q * a + Polynomial.C m * r).natDegree ≤ f0.natDegree := by
    rfl
  have hg_bound : (q * b + Polynomial.C m * s).natDegree ≤ g0.natDegree := by
    rfl
  have hred :=
    sylvester_commonFactor_colReduce q a b r s m hd ha hb hf_bound hg_bound
  have hdetA :
      A.det = (Polynomial.sylvester f0 g0 f0.natDegree g0.natDegree).det := by
    dsimp [A, S, T]
    have hdet := hred.1
    rw [hb_pivot, one_pow, one_mul] at hdet
    exact hdet
  have hpiv_inj :
      Function.Injective
        (fun t : Fin d =>
          ((⟨g0.natDegree - d + (t : ℕ),
              by have := t.is_lt; omega⟩ : Fin g0.natDegree).natAdd f0.natDegree :
            Fin (f0.natDegree + g0.natDegree))) := by
    intro x y hxy
    apply Fin.ext
    have hnat :
        f0.natDegree + (g0.natDegree - d + (x : ℕ)) =
          f0.natDegree + (g0.natDegree - d + (y : ℕ)) := by
      simpa only [Fin.ext_iff, Fin.coe_natAdd] using hxy
    have hnat' :
        g0.natDegree - d + (x : ℕ) = g0.natDegree - d + (y : ℕ) :=
      Nat.add_left_cancel hnat
    exact Nat.add_left_cancel hnat'
  have hcols :
      ∀ (t : Fin d) (i : Fin (f0.natDegree + g0.natDegree)),
        m ∣ A i
          ((⟨g0.natDegree - d + (t : ℕ),
              by have := t.is_lt; omega⟩ : Fin g0.natDegree).natAdd f0.natDegree) := by
    intro t i
    dsimp [A, S, T]
    exact hred.2 t i
  have hA : m ^ d ∣ A.det :=
    det_dvd_of_cols_dvd m A
      (fun t : Fin d =>
        ((⟨g0.natDegree - d + (t : ℕ),
            by have := t.is_lt; omega⟩ : Fin g0.natDegree).natAdd f0.natDegree :
          Fin (f0.natDegree + g0.natDegree)))
      hpiv_inj hcols
  rw [hdetA] at hA
  simpa [Polynomial.resultant, f0, g0] using hA

/--
Monic-cofactor form of `commonFactor_dvd_resultant`: if the right cofactor `b`
is monic and has the expected degree `g.natDegree - d`, then the pivot
coefficient required by the column reduction is automatically `1`.
-/
theorem commonFactor_dvd_resultant_of_monic_cofactor
    (f g q a b r s : Polynomial ℤ) (m : ℤ) {d : Nat}
    (hf_wit : f = q * a + Polynomial.C m * r)
    (hg_wit : g = q * b + Polynomial.C m * s)
    (hq_monic : q.Monic)
    (hq_deg : q.natDegree = d)
    (hd : d ≤ g.natDegree)
    (ha : a.natDegree + d ≤ f.natDegree)
    (hb_degree : b.natDegree + d = g.natDegree)
    (hb_monic : b.Monic) :
    m ^ d ∣ Polynomial.resultant f g := by
  have hb : b.natDegree + d ≤ g.natDegree := le_of_eq hb_degree
  have hb_pivot : b.coeff (g.natDegree - d) = 1 := by
    have hsub : g.natDegree - d = b.natDegree := by omega
    rw [hsub]
    exact hb_monic.leadingCoeff
  exact commonFactor_dvd_resultant f g q a b r s m hf_wit hg_wit hq_monic hq_deg
    hd ha hb hb_pivot

/--
Degree-controlled witness from a `ZMod n` divisibility by a *monic* `q`.

Unlike `exists_witnesses_of_map_dvd_zmod`, which lifts an arbitrary modular
quotient, this uses honest monic division: the quotient is `f /ₘ q` (so its
degree is `f.natDegree - q.natDegree`) and the remainder `f %ₘ q` is
coefficientwise divisible by `n`, packaged as `Polynomial.C (n : ℤ) * s`. The
degree control is what the Sylvester column reduction in
`commonFactor_dvd_resultant` needs.
-/
private theorem exists_divByMonic_witness {f q : Polynomial ℤ} {n : ℕ}
    (hq : q.Monic)
    (hdvd : q.map (Int.castRingHom (ZMod n)) ∣
            f.map (Int.castRingHom (ZMod n))) :
    ∃ s : Polynomial ℤ, f = q * (f /ₘ q) + Polynomial.C (n : ℤ) * s := by
  have hqmap : (q.map (Int.castRingHom (ZMod n))).Monic := hq.map _
  -- The monic-division remainder vanishes modulo `n`.
  have hrem0 : (f %ₘ q).map (Int.castRingHom (ZMod n)) = 0 := by
    rw [Polynomial.map_modByMonic (Int.castRingHom (ZMod n)) hq]
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hqmap).mpr hdvd
  -- Hence each coefficient is divisible by `n`, so `C n` divides `f %ₘ q`.
  have hCdvd : Polynomial.C (n : ℤ) ∣ (f %ₘ q) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro k
    have hc : (((f %ₘ q).coeff k : ℤ) : ZMod n) = 0 := by
      have h0 : ((f %ₘ q).map (Int.castRingHom (ZMod n))).coeff k = 0 := by
        rw [hrem0]; simp
      rwa [Polynomial.coeff_map] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp hc
  obtain ⟨s, hs⟩ := hCdvd
  refine ⟨s, ?_⟩
  have hsplit := Polynomial.modByMonic_add_div f q
  rw [hs] at hsplit
  linear_combination -hsplit

/--
BHKS Lemma 3.2 modular-resultant divisibility, in the form downstream
Hensel/CLD code consumes.

If a monic degree-`d` polynomial `q` divides both `f` and `g` after reduction
modulo `p ^ k`, with `f` monic and `d` not exceeding either degree, then
`p ^ (k * d)` divides the integer resultant of `f` and `g`.

The exponent is `k * d`, not merely `k`: the monic common factor `q` contributes
`d` independent Sylvester column directions, each carrying one factor of the
modulus `p ^ k`, so the column reduction (`commonFactor_dvd_resultant`) turns
those `d` directions into `(p ^ k) ^ d = p ^ (k * d)` dividing the resultant.
Monicity of `f` supplies the unit pivot the reduction needs; the result is read
off the swapped pair via `Polynomial.resultant_comm`.
-/
theorem pow_dvd_resultant_of_map_dvd
    {p k : ℕ} {f g q : Polynomial ℤ} {d : ℕ}
    (hq_monic : q.Monic)
    (hq_deg : q.natDegree = d)
    (hf_monic : f.Monic)
    (hdf : d ≤ f.natDegree)
    (hdg : d ≤ g.natDegree)
    (hf_dvd : q.map (Int.castRingHom (ZMod (p ^ k))) ∣
              f.map (Int.castRingHom (ZMod (p ^ k))))
    (hg_dvd : q.map (Int.castRingHom (ZMod (p ^ k))) ∣
              g.map (Int.castRingHom (ZMod (p ^ k)))) :
    ((p ^ (k * d) : ℕ) : ℤ) ∣ Polynomial.resultant f g := by
  -- Degree-controlled monic-division witnesses for both polynomials.
  obtain ⟨r, hr⟩ := exists_divByMonic_witness hq_monic hg_dvd
  obtain ⟨s, hs⟩ := exists_divByMonic_witness hq_monic hf_dvd
  -- `q.degree ≤ f.degree`, needed for the leading-coefficient transfer.
  have hdeg_le : q.degree ≤ f.degree := by
    rw [Polynomial.degree_eq_natDegree hq_monic.ne_zero,
        Polynomial.degree_eq_natDegree hf_monic.ne_zero, hq_deg]
    exact_mod_cast hdf
  -- The pivot cofactor `f /ₘ q` is monic because `f` is.
  have hb_monic : (f /ₘ q).Monic := by
    have := Polynomial.leadingCoeff_divByMonic_of_monic hq_monic hdeg_le
    exact this.trans hf_monic
  -- Apply the column-reduction lemma to the swapped pair `(g, f)`, so the monic
  -- cofactor `f /ₘ q` of `f` plays the pivot role.
  have key : ((p ^ k : ℕ) : ℤ) ^ d ∣ Polynomial.resultant g f := by
    apply commonFactor_dvd_resultant_of_monic_cofactor g f q (g /ₘ q) (f /ₘ q)
      r s ((p ^ k : ℕ) : ℤ) (d := d) hr hs hq_monic hq_deg hdf
    · rw [Polynomial.natDegree_divByMonic g hq_monic, hq_deg]; omega
    · rw [Polynomial.natDegree_divByMonic f hq_monic, hq_deg]; omega
    · exact hb_monic
  -- Convert `(p ^ k) ^ d` to `p ^ (k * d)` and read off `resultant f g` via comm.
  have hcast : ((p ^ (k * d) : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) ^ d := by
    rw [pow_mul, Nat.cast_pow]
  rw [hcast, Polynomial.resultant_comm]
  exact key.mul_left _

/--
The CLD-syzygy column-reduction transform for the Sylvester matrix.

In the `Fin (m + n)` layout of `sylvester f g m n`, the *left* block columns
`d, d+1, …, 2d-1` are the pivot columns. Column `d + t` carries the coordinate
vector of the shifted CLD-syzygy direction `(q * X^t, -q' * X^t)` in
`degreeLT.basisProd`: its left `m` entries are the coefficients of the monic
`q * X^t`, its right `n` entries those of `-q' * X^t`. Every other column is the
identity column.

Right-multiplying `sylvester f g m n` by this matrix replaces each pivot column
with the syzygy combination `S.mulVec (direction)` (entrywise divisible by the
syzygy scalar, via `sylvester_mulVec_cld_syzygy`) while leaving the others
fixed. The matrix is block-lower-triangular for the left/right partition — its
top-right block vanishes because the right columns stay identity — and its left
diagonal block is upper triangular with the monic leading `1` of `q * X^t` on
the diagonal, so `det = 1`. Unlike `colReduceTransform`, the monic pivot here is
the *left* component `q`, so the matrix is not triangular under the natural
order; the determinant is read off the block decomposition.
-/
def cldColReduceTransform {R : Type*} [CommRing R] (q : Polynomial R) (m n d : Nat) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  Matrix.of fun i j =>
    j.addCases
      (fun j₁ =>
        if d ≤ (j₁ : ℕ) ∧ (j₁ : ℕ) < 2 * d then
          i.addCases
            (fun i₁ => (q * Polynomial.X ^ ((j₁ : ℕ) - d)).coeff i₁)
            (fun i₂ => (-Polynomial.derivative q * Polynomial.X ^ ((j₁ : ℕ) - d)).coeff i₂)
        else if i = j then 1 else 0)
      (fun _j₂ => if i = j then 1 else 0)

set_option maxHeartbeats 400000 in
/-- The determinant of `cldColReduceTransform` is `1`: the left diagonal block is
upper triangular with the monic leading coefficient of `q` on its diagonal, and
the top-right block vanishes (the right columns are identity). -/
theorem cldColReduceTransform_det {R : Type*} [CommRing R] (q : Polynomial R)
    {m n d : Nat} (hq_monic : q.Monic) (hq_deg : q.natDegree = d) :
    (cldColReduceTransform q m n d).det = 1 := by
  classical
  set TLL : Matrix (Fin m) (Fin m) R := Matrix.of fun i₁ j₁ =>
    if d ≤ (j₁ : ℕ) ∧ (j₁ : ℕ) < 2 * d then (q * Polynomial.X ^ ((j₁ : ℕ) - d)).coeff i₁
    else if i₁ = j₁ then 1 else 0 with hTLL
  set TRL : Matrix (Fin n) (Fin m) R := Matrix.of fun i₂ j₁ =>
    if d ≤ (j₁ : ℕ) ∧ (j₁ : ℕ) < 2 * d then
      (-Polynomial.derivative q * Polynomial.X ^ ((j₁ : ℕ) - d)).coeff i₂
    else 0 with hTRL
  have hblock : cldColReduceTransform q m n d
      = (Matrix.fromBlocks TLL 0 TRL (1 : Matrix (Fin n) (Fin n) R)).reindex
          finSumFinEquiv finSumFinEquiv := by
    ext i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    induction j using Fin.addCases with
    | left j₁ =>
        rw [finSumFinEquiv_symm_apply_castAdd, cldColReduceTransform, Matrix.of_apply,
          Fin.addCases_left]
        induction i using Fin.addCases with
        | left i₁ =>
            rw [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, hTLL,
              Matrix.of_apply]
            by_cases hpiv : d ≤ (j₁ : ℕ) ∧ (j₁ : ℕ) < 2 * d
            · simp only [if_pos hpiv, Fin.addCases_left]
            · simp only [if_neg hpiv, Fin.ext_iff, Fin.val_castAdd]
        | right i₂ =>
            rw [finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, hTRL,
              Matrix.of_apply]
            by_cases hpiv : d ≤ (j₁ : ℕ) ∧ (j₁ : ℕ) < 2 * d
            · simp only [if_pos hpiv, Fin.addCases_right]
            · simp only [if_neg hpiv]
              refine if_neg (fun h => ?_)
              have := j₁.is_lt
              simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd] at h
              omega
    | right j₂ =>
        rw [finSumFinEquiv_symm_apply_natAdd, cldColReduceTransform, Matrix.of_apply,
          Fin.addCases_right]
        induction i using Fin.addCases with
        | left i₁ =>
            rw [finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₂,
              Matrix.zero_apply]
            refine if_neg (fun h => ?_)
            have := i₁.is_lt
            simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h
            omega
        | right i₂ =>
            rw [finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂,
              Matrix.one_apply]
            simp only [Fin.ext_iff, Fin.val_natAdd, add_right_inj]
  rw [hblock, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  -- The left diagonal block is upper triangular with unit diagonal.
  have htri : TLL.BlockTriangular id := by
    intro i₁ j₁ hlt
    simp only [id_eq, Fin.lt_def] at hlt
    rw [hTLL, Matrix.of_apply]
    by_cases hpiv : d ≤ (j₁ : ℕ) ∧ (j₁ : ℕ) < 2 * d
    · rw [if_pos hpiv, Polynomial.coeff_mul_X_pow']
      split_ifs with hk
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hq_deg]; omega
      · rfl
    · rw [if_neg hpiv]
      exact if_neg (fun h => by rw [h] at hlt; exact lt_irrefl _ hlt)
  rw [Matrix.det_of_upperTriangular htri]
  apply Finset.prod_eq_one
  intro i₁ _
  rw [hTLL, Matrix.of_apply]
  by_cases hpiv : d ≤ (i₁ : ℕ) ∧ (i₁ : ℕ) < 2 * d
  · rw [if_pos hpiv, Polynomial.coeff_mul_X_pow', if_pos (Nat.sub_le _ _)]
    have hidx : (i₁ : ℕ) - ((i₁ : ℕ) - d) = d := by omega
    rw [hidx, ← hq_deg]
    exact hq_monic.coeff_natDegree
  · simp [hpiv]

/-- The pivot column `d + t` (in the left block) of `cldColReduceTransform` is the
coordinate vector of the shifted CLD-syzygy direction `(q * X^t, -q' * X^t)` in
`degreeLT.basisProd`. -/
theorem cldColReduceTransform_pivot_col {R : Type*} [CommRing R] (q : Polynomial R)
    {m n d : Nat} (t : Nat) (htd : t < d) (htm : d + t < m)
    (hl : q * Polynomial.X ^ t ∈ Polynomial.degreeLT R m)
    (hr : -Polynomial.derivative q * Polynomial.X ^ t ∈ Polynomial.degreeLT R n) :
    (fun k => cldColReduceTransform q m n d k ((⟨d + t, htm⟩ : Fin m).castAdd n))
      = (Polynomial.degreeLT.basisProd R m n).repr
          (⟨q * Polynomial.X ^ t, hl⟩,
           ⟨-Polynomial.derivative q * Polynomial.X ^ t, hr⟩) := by
  funext k
  rw [cldColReduceTransform, Matrix.of_apply, Fin.addCases_left]
  rw [if_pos ⟨Nat.le_add_right d t, show d + t < 2 * d by omega⟩]
  have hexp : d + t - d = t := by omega
  rw [hexp]
  induction k using Fin.addCases with
  | left k₁ => rw [Fin.addCases_left, basisProd_repr_castAdd]
  | right k₂ => rw [Fin.addCases_right, basisProd_repr_natAdd]

/--
CLD-syzygy resultant divisibility (BHKS Lemma 3.2 core, scalar form).

If a monic degree-`d` polynomial `q` and a witness `z` record the CLD syzygy
`g * q - f * q' = C c * z`, then `c ^ d` divides the integer resultant of `f`
and `g`. Crucially, no divisibility hypothesis `q ∣ g` (or its modular form) is
assumed: the syzygy provides `d` Sylvester column directions
`(q * X^t, -q' * X^t)` whose images are `c`-multiples, and the monic leading `1`
of each `q * X^t` makes the column-reduction transform determinant-preserving.

The degree bounds are intrinsic to the syzygy route: the `d` shifts of `q * X^t`
must lie in `degreeLT f.natDegree` (forcing `2 * d ≤ f.natDegree`), and the `d`
shifts of `-q' * X^t` must lie in `degreeLT g.natDegree` (forcing
`2 * d ≤ g.natDegree + 1`). The first is the `deg input ≥ 2d` constraint flagged
in BHKS Lemma 3.2; the second is the analogous bound on the auxiliary-polynomial
degree, which downstream callers must also discharge (or fall back to the
cut-based argument for small factors).
-/
theorem cld_syzygy_dvd_resultant
    (f g q z : Polynomial ℤ) (c : ℤ) {d : Nat}
    (hq_monic : q.Monic)
    (hq_deg : q.natDegree = d)
    (hsyz : g * q - f * Polynomial.derivative q = Polynomial.C c * z)
    (hf_deg : 2 * d ≤ f.natDegree)
    (hg_deg : 2 * d ≤ g.natDegree + 1) :
    c ^ d ∣ Polynomial.resultant f g := by
  classical
  let A := Polynomial.sylvester f g f.natDegree g.natDegree
      * cldColReduceTransform q f.natDegree g.natDegree d
  let col : Fin d → Fin (f.natDegree + g.natDegree) := fun t =>
    (⟨d + (t : ℕ), by have := t.is_lt; omega⟩ : Fin f.natDegree).castAdd g.natDegree
  have hdetA :
      A.det = (Polynomial.sylvester f g f.natDegree g.natDegree).det := by
    dsimp only [A]
    rw [Matrix.det_mul, cldColReduceTransform_det q hq_monic hq_deg, mul_one]
  have hcol_inj : Function.Injective col := by
    intro x y hxy
    apply Fin.ext
    have hnat : d + (x : ℕ) = d + (y : ℕ) := by
      simpa only [col, Fin.ext_iff, Fin.val_castAdd] using hxy
    omega
  have hcols : ∀ (t : Fin d) (i : Fin (f.natDegree + g.natDegree)), c ∣ A i (col t) := by
    intro t i
    have htd : (t : ℕ) < d := t.is_lt
    have htm : d + (t : ℕ) < f.natDegree := by omega
    have hl : q * Polynomial.X ^ (t : ℕ) ∈ Polynomial.degreeLT ℤ f.natDegree := by
      apply mul_X_pow_mem_degreeLT_of_natDegree_lt
      have h1 : (q * Polynomial.X ^ (t : ℕ)).natDegree ≤ q.natDegree + (t : ℕ) :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add_left (Polynomial.natDegree_X_pow_le _) _)
      have h2 : q.natDegree + (t : ℕ) < f.natDegree := by rw [hq_deg]; omega
      exact lt_of_le_of_lt h1 h2
    have hr : -Polynomial.derivative q * Polynomial.X ^ (t : ℕ)
        ∈ Polynomial.degreeLT ℤ g.natDegree := by
      apply neg_mul_X_pow_mem_degreeLT_of_natDegree_lt
      have h1 : (Polynomial.derivative q * Polynomial.X ^ (t : ℕ)).natDegree
            ≤ (Polynomial.derivative q).natDegree + (t : ℕ) :=
        Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add_left (Polynomial.natDegree_X_pow_le _) _)
      have hqd : (Polynomial.derivative q).natDegree ≤ d - 1 := by
        have := Polynomial.natDegree_derivative_le q; rw [hq_deg] at this; exact this
      have h2 : (Polynomial.derivative q).natDegree + (t : ℕ) < g.natDegree := by omega
      exact lt_of_le_of_lt h1 h2
    have hcoleq : A i (col t)
        = (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
            ((Polynomial.degreeLT.basisProd ℤ f.natDegree g.natDegree).repr
              (⟨q * Polynomial.X ^ (t : ℕ), hl⟩,
               ⟨-Polynomial.derivative q * Polynomial.X ^ (t : ℕ), hr⟩)) i := by
      dsimp only [A, col]
      rw [← cldColReduceTransform_pivot_col q (t : ℕ) htd htm hl hr]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hcoleq]
    exact sylvester_mulVec_cld_syzygy f g q z c hsyz hl hr le_rfl le_rfl i
  exact dvd_resultant_of_sylvester_cols f g c A col hcol_inj hdetA hcols

/--
Prime-power form of `cld_syzygy_dvd_resultant` (BHKS Lemma 3.2, as consumed by
the Hensel/CLD layer). With the syzygy scalar `c = p ^ k`, the `d` column
directions each carry one factor of `p ^ k`, so `p ^ (k * d)` divides the
resultant. No hypothesis that the selected factor divides the auxiliary
polynomial modulo `p ^ k` is required.
-/
theorem cld_syzygy_pow_dvd_resultant
    {p k : Nat} (f g q z : Polynomial ℤ) {d : Nat}
    (hq_monic : q.Monic)
    (hq_deg : q.natDegree = d)
    (hsyz : g * q - f * Polynomial.derivative q
      = Polynomial.C ((p ^ k : Nat) : ℤ) * z)
    (hf_deg : 2 * d ≤ f.natDegree)
    (hg_deg : 2 * d ≤ g.natDegree + 1) :
    ((p ^ (k * d) : Nat) : ℤ) ∣ Polynomial.resultant f g := by
  have hbase : ((p ^ k : Nat) : ℤ) ^ d ∣ Polynomial.resultant f g :=
    cld_syzygy_dvd_resultant f g q z _ hq_monic hq_deg hsyz hf_deg hg_deg
  have hcast : ((p ^ (k * d) : Nat) : ℤ) = ((p ^ k : Nat) : ℤ) ^ d := by
    rw [pow_mul, Nat.cast_pow]
  rw [hcast]; exact hbase

end

end HexBerlekampZassenhausMathlib
