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

end

end HexBerlekampZassenhausMathlib
