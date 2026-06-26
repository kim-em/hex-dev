module

public import HexHenselMathlib.Basic
public import HexPolyMathlib.Basic
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Field.ZMod

public section

/-!
Mathlib-facing correctness and uniqueness theorem surface for executable
Hensel lifting.

The statements in this module transfer the `Hex.ZPoly` Hensel API through
`HexPolyMathlib.toPolynomial`, while keeping all new content proof-only.
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

/--
Coefficientwise executable congruence modulo `m` transfers to equality after
mapping the corresponding Mathlib polynomials to `ZMod m`.
-/
theorem zpoly_congr_toPolynomial_map_eq
    (f g : Hex.ZPoly) (m : Nat)
    (hcongr : Hex.ZPoly.congr f g m) :
    let φ := Int.castRingHom (ZMod m)
    (HexPolyMathlib.toPolynomial f).map φ =
      (HexPolyMathlib.toPolynomial g).map φ := by
  apply Polynomial.ext
  intro n
  rw [coeff_map_intCastRingHom_eq_iff_dvd_sub,
      HexPolyMathlib.coeff_toPolynomial,
      HexPolyMathlib.coeff_toPolynomial]
  exact Int.dvd_of_emod_eq_zero (hcongr n)

/-- The iterative executable lift gives a factorization of `f` over Mathlib polynomials modulo `p^k`. -/
theorem hensel_correct
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g)
    (hgdeg : 0 < g.degree?.getD 0) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod (p ^ k))
    (HexPolyMathlib.toPolynomial r.g).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (HexPolyMathlib.toPolynomial f).map φ := by
  let r := Hex.ZPoly.henselLift p k f g h s t
  let φ := Int.castRingHom (ZMod (p ^ k))
  have hcongr :
      Hex.ZPoly.congr (r.g * r.h) f (p ^ k) := by
    simpa [r] using
      Hex.ZPoly.henselLift_congr_of_base p k f g h s t hk hp hprod hbez hmonic hgdeg
  have hmap := zpoly_congr_toPolynomial_map_eq (r.g * r.h) f (p ^ k) hcongr
  simpa [r, φ, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul] using hmap

/-- The iterative executable lift extends the input factorization modulo `p`. -/
theorem hensel_extends
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (_hprod : Hex.ZPoly.congr (g * h) f p)
    (_hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (_hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod p)
    (HexPolyMathlib.toPolynomial r.g).map φ =
        (HexPolyMathlib.toPolynomial g).map φ ∧
      (HexPolyMathlib.toPolynomial r.h).map φ =
        (HexPolyMathlib.toPolynomial h).map φ := by
  refine ⟨?_, ?_⟩
  · exact zpoly_congr_toPolynomial_map_eq
      (Hex.ZPoly.henselLift p k f g h s t).g g p
      (Hex.ZPoly.henselLift_g_congr_mod_base p k f g h s t hk)
  · exact zpoly_congr_toPolynomial_map_eq
      (Hex.ZPoly.henselLift p k f g h s t).h h p
      (Hex.ZPoly.henselLift_h_congr_mod_base p k f g h s t hk)

/-- The iterative executable lift preserves the Mathlib degree of the monic lifted factor. -/
theorem hensel_degree
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g)
    (hgdeg : 0 < g.degree?.getD 0) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    (HexPolyMathlib.toPolynomial r.g).natDegree =
      (HexPolyMathlib.toPolynomial g).natDegree := by
  let r := Hex.ZPoly.henselLift p k f g h s t
  have hdegree :
      r.g.degree? = g.degree? := by
    simpa [r] using
      Hex.ZPoly.henselLift_degree?_of_base p k f g h s t hk hp hprod hbez hmonic hgdeg
  simp [r, HexPolyMathlib.natDegree_toPolynomial, hdegree]

/--
Equality of Mathlib polynomial reductions modulo `m` gives the executable
coefficientwise congruence used by `Hex.ZPoly`.
-/
theorem zpoly_congr_of_toPolynomial_map_eq
    (f g : Hex.ZPoly) (m : Nat)
    (hmap :
      let φ := Int.castRingHom (ZMod m)
      (HexPolyMathlib.toPolynomial f).map φ =
        (HexPolyMathlib.toPolynomial g).map φ) :
    Hex.ZPoly.congr f g m := by
  intro n
  have hcoeff := Polynomial.ext_iff.mp hmap n
  rw [coeff_map_intCastRingHom_eq_iff_dvd_sub,
      HexPolyMathlib.coeff_toPolynomial,
      HexPolyMathlib.coeff_toPolynomial] at hcoeff
  exact Int.emod_eq_zero_of_dvd hcoeff

/-- The executable monic predicate transfers to Mathlib's polynomial monic predicate. -/
theorem toPolynomial_monic_of_dense_monic
    (f : Hex.ZPoly) (hmonic : Hex.DensePoly.Monic f) :
    (HexPolyMathlib.toPolynomial f).Monic := by
  show (HexPolyMathlib.toPolynomial f).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hmonic

/--
An executable Bezout congruence gives coprimality of the corresponding Mathlib
polynomials after reduction modulo `p`.
-/
private theorem isCoprime_of_zpoly_bezout
    (p : Nat) [Hex.ZMod64.Bounds p]
    (g h s t : Hex.ZPoly)
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 p) :
    let φ := Int.castRingHom (ZMod p)
    IsCoprime
      ((HexPolyMathlib.toPolynomial g).map φ)
      ((HexPolyMathlib.toPolynomial h).map φ) := by
  intro φ
  refine ⟨(HexPolyMathlib.toPolynomial s).map φ,
    (HexPolyMathlib.toPolynomial t).map φ, ?_⟩
  have hmap := zpoly_congr_toPolynomial_map_eq (s * g + t * h) 1 p hbez
  have hone : HexPolyMathlib.toPolynomial (1 : Hex.ZPoly) = 1 := by
    change HexPolyMathlib.toPolynomial (Hex.DensePoly.C (1 : Int)) = 1
    simp
  simpa [HexPolyMathlib.toPolynomial_add, HexPolyMathlib.toPolynomial_mul,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, hone] using hmap

/--
Monic integer polynomials with the same prime-field reduction have the same
degree.
-/
private theorem natDegree_eq_of_monic_map_eq
    (p : Nat) [Fact (Nat.Prime p)]
    {g h : Polynomial ℤ}
    (hg : g.Monic) (hh : h.Monic)
    (hmap :
      g.map (Int.castRingHom (ZMod p)) =
        h.map (Int.castRingHom (ZMod p))) :
    g.natDegree = h.natDegree := by
  have hne : (1 : ZMod p) ≠ 0 := by
    exact one_ne_zero
  apply le_antisymm
  · by_contra hle
    have hlt : h.natDegree < g.natDegree := Nat.lt_of_not_ge hle
    have hcoeff := Polynomial.ext_iff.mp hmap g.natDegree
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hg.coeff_natDegree,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at hcoeff
    simp at hcoeff
  · by_contra hle
    have hlt : g.natDegree < h.natDegree := Nat.lt_of_not_ge hle
    have hcoeff := Polynomial.ext_iff.mp hmap h.natDegree
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hh.coeff_natDegree,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at hcoeff
    simp at hcoeff

/--
The quadratic executable step gives a Mathlib factorization modulo `m*m`.
This is the Mathlib-facing form of `Hex.ZPoly.quadraticHenselStep_factor_spec`.
-/
theorem quadraticHenselStep_factor_correct
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 0 < m)
    (hprod : Hex.ZPoly.congr (g * h) f m)
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    let φ := Int.castRingHom (ZMod (m * m))
    (HexPolyMathlib.toPolynomial r.g).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (HexPolyMathlib.toPolynomial f).map φ := by
  let r := Hex.ZPoly.quadraticHenselStep m f g h s t
  let φ := Int.castRingHom (ZMod (m * m))
  have hcongr :
      Hex.ZPoly.congr (r.g * r.h) f (m * m) := by
    simpa [r] using
      Hex.ZPoly.quadraticHenselStep_factor_spec m f g h s t hm hprod hbez hmonic
  have hmap := zpoly_congr_toPolynomial_map_eq (r.g * r.h) f (m * m) hcongr
  simpa [r, φ, HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul] using hmap

/--
The quadratic executable step updates Bezout witnesses modulo `m*m`.
This is the Mathlib-facing form of `Hex.ZPoly.quadraticHenselStep_bezout_spec`.
-/
theorem quadraticHenselStep_bezout_correct
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 0 < m)
    (hprod : Hex.ZPoly.congr (g * h) f m)
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    let φ := Int.castRingHom (ZMod (m * m))
    (HexPolyMathlib.toPolynomial r.s).map φ *
        (HexPolyMathlib.toPolynomial r.g).map φ +
      (HexPolyMathlib.toPolynomial r.t).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (1 : Polynomial (ZMod (m * m))) := by
  let r := Hex.ZPoly.quadraticHenselStep m f g h s t
  let φ := Int.castRingHom (ZMod (m * m))
  by_cases hm1 : 1 < m
  · have hcongr :
        Hex.ZPoly.congr (r.s * r.g + r.t * r.h) 1 (m * m) := by
      simpa [r] using
        Hex.ZPoly.quadraticHenselStep_bezout_spec m f g h s t hm1 hprod hbez hmonic
    have hmap := zpoly_congr_toPolynomial_map_eq (r.s * r.g + r.t * r.h) 1 (m * m) hcongr
    have hone : HexPolyMathlib.toPolynomial (1 : Hex.ZPoly) = 1 := by
      change HexPolyMathlib.toPolynomial (Hex.DensePoly.C (1 : Int)) = 1
      simp
    simpa [r, φ, HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add,
      Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one, hone] using hmap
  · have hm_eq : m = 1 := by omega
    subst m
    haveI : Subsingleton (ZMod (1 * 1)) := ZMod.subsingleton_iff.mpr (by norm_num)
    apply Polynomial.ext
    intro n
    exact Subsingleton.elim _ _

/-- The quadratic step preserves monicity on the lifted `g` factor in Mathlib form.

The executable substrate (`Hex.ZPoly.quadraticHenselStep_monic`) requires `1 < m`:
at `m = 1` every `*ModSquare` operation reduces modulo `1`, collapsing the lifted
factor to the zero polynomial, which is not monic. So the hypothesis is `1 < m`. -/
theorem quadraticHenselStep_monic
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 1 < m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    (HexPolyMathlib.toPolynomial r.g).Monic :=
  toPolynomial_monic_of_dense_monic _
    (Hex.ZPoly.quadraticHenselStep_monic m f g h s t hm hmonic)

/--
If two integer polynomials reduce to the same element of `Polynomial (ZMod (p^k))`,
their difference factors as `C ((p^k : ℕ) : ℤ)` times some integer polynomial.
-/
private lemma exists_C_pow_mul_of_map_pow_eq {p k : ℕ} {f g : Polynomial ℤ}
    (heq : f.map (Int.castRingHom (ZMod (p ^ k))) =
      g.map (Int.castRingHom (ZMod (p ^ k)))) :
    ∃ A : Polynomial ℤ, f - g = Polynomial.C ((p ^ k : ℕ) : ℤ) * A := by
  have hcoeff : ∀ n, ((p ^ k : ℕ) : ℤ) ∣ (f - g).coeff n := fun n => by
    rw [Polynomial.coeff_sub]
    have hn := Polynomial.ext_iff.mp heq n
    rwa [coeff_map_intCastRingHom_eq_iff_dvd_sub] at hn
  exact (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcoeff

/--
If `A` vanishes modulo `p`, then `C ((p^k : ℕ) : ℤ) * A` vanishes modulo `p^(k+1)`.
-/
private lemma map_C_pow_mul_eq_zero_of_map_modP_eq_zero
    {p k : ℕ} (A : Polynomial ℤ)
    (hA : A.map (Int.castRingHom (ZMod p)) = 0) :
    (Polynomial.C ((p ^ k : ℕ) : ℤ) * A).map
        (Int.castRingHom (ZMod (p ^ (k + 1)))) = 0 := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_zero, coeff_map_intCastRingHom_eq_zero_iff_dvd,
    Polynomial.coeff_C_mul]
  have hp_dvd : (p : ℤ) ∣ A.coeff n :=
    (coeff_map_intCastRingHom_eq_zero_iff_dvd A p n).mp <| by
      rw [hA]; simp
  push_cast
  rw [pow_succ]
  exact mul_dvd_mul_left _ hp_dvd

/-- Coprime monic factorizations with the same reduction modulo `p` are unique modulo `p^k`.

The `0 < k` hypothesis is part of the calling convention; the proof works for
`k = 0` too because `ZMod 1` is the zero ring. The `hh1` hypothesis is similarly
redundant: the cancellation step uses `hg1` to substitute `g'` for `g` mod `p`,
which suffices in conjunction with `hcop` and the monic degree bound. -/
theorem hensel_unique (f g h g' h' : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (_hk : 0 < k)
    (hg : g.Monic) (hg' : g'.Monic)
    (hdeg : g.natDegree = g'.natDegree)
    (hprod :
      let φ := Int.castRingHom (ZMod (p ^ k))
      (g.map φ) * (h.map φ) = f.map φ)
    (hprod' :
      let φ := Int.castRingHom (ZMod (p ^ k))
      (g'.map φ) * (h'.map φ) = f.map φ)
    (hg1 :
      let φ := Int.castRingHom (ZMod p)
      g.map φ = g'.map φ)
    (_hh1 :
      let φ := Int.castRingHom (ZMod p)
      h.map φ = h'.map φ)
    (hcop :
      let φ := Int.castRingHom (ZMod p)
      IsCoprime (g.map φ) (h.map φ)) :
    let φ := Int.castRingHom (ZMod (p ^ k))
    g.map φ = g'.map φ ∧ h.map φ = h'.map φ := by
  clear _hk
  simp only at hprod hprod' hg1 hcop ⊢
  induction k with
  | zero =>
    haveI : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (by simp)
    refine ⟨?_, ?_⟩ <;>
    · apply Polynomial.ext; intro n
      exact Subsingleton.elim _ _
  | succ k ih =>
    -- Step 1: Derive level-`k` versions of `hprod`, `hprod'` by composing
    -- with the canonical reduction `ZMod (p^(k+1)) →+* ZMod (p^k)`.
    have hprod_k :
        (g.map (Int.castRingHom (ZMod (p ^ k)))) *
            (h.map (Int.castRingHom (ZMod (p ^ k)))) =
          f.map (Int.castRingHom (ZMod (p ^ k))) := by
      have h := congr_arg
        (Polynomial.map
          (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))))
        hprod
      simpa [Polynomial.map_mul, polynomial_map_zmod_pow_succ_to_pow] using h
    have hprod'_k :
        (g'.map (Int.castRingHom (ZMod (p ^ k)))) *
            (h'.map (Int.castRingHom (ZMod (p ^ k)))) =
          f.map (Int.castRingHom (ZMod (p ^ k))) := by
      have h := congr_arg
        (Polynomial.map
          (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))))
        hprod'
      simpa [Polynomial.map_mul, polynomial_map_zmod_pow_succ_to_pow] using h
    obtain ⟨hg_k, hh_k⟩ := ih hprod_k hprod'_k
    -- Step 2: Extract `A, B : Polynomial ℤ` with `g - g' = C (p^k) * A`,
    -- `h - h' = C (p^k) * B`.
    obtain ⟨A, hA⟩ := exists_C_pow_mul_of_map_pow_eq hg_k
    obtain ⟨B, hB⟩ := exists_C_pow_mul_of_map_pow_eq hh_k
    -- Step 3: Show the level-`k+1` product difference vanishes.
    have hgh_diff_zero :
        (g * h - g' * h').map (Int.castRingHom (ZMod (p ^ (k + 1)))) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, hprod,
        hprod', sub_self]
    -- The product difference factors as `C (p^k) * (A*h + g'*B)`.
    have hexpand : g * h - g' * h' =
        Polynomial.C ((p ^ k : ℕ) : ℤ) * (A * h + g' * B) := by
      have hrearr : g * h - g' * h' = (g - g') * h + g' * (h - h') := by ring
      rw [hrearr, hA, hB]; ring
    have hkey : (Polynomial.C ((p ^ k : ℕ) : ℤ) * (A * h + g' * B)).map
        (Int.castRingHom (ZMod (p ^ (k + 1)))) = 0 := by
      rw [← hexpand]; exact hgh_diff_zero
    -- Step 4: Show the cofactor `A*h + g'*B` vanishes modulo `p`.
    -- The level-`p^(k+1)` equation `C (p^k) * (A*h + g'*B) ≡ 0` says
    -- `p^(k+1) ∣ p^k · (coeff n)` integerwise, hence `p ∣ (coeff n)`.
    have hkey_modp :
        (A * h + g' * B).map (Int.castRingHom (ZMod p)) = 0 := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_zero, coeff_map_intCastRingHom_eq_zero_iff_dvd]
      have hcoeff := Polynomial.ext_iff.mp hkey n
      rw [Polynomial.coeff_zero, coeff_map_intCastRingHom_eq_zero_iff_dvd,
        Polynomial.coeff_C_mul] at hcoeff
      have hp_pos : 0 < (p : ℤ) := by exact_mod_cast (Fact.out (p := Nat.Prime p)).pos
      have hpk_ne : ((p : ℤ) ^ k) ≠ 0 := pow_ne_zero k hp_pos.ne'
      push_cast at hcoeff
      rw [pow_succ, mul_dvd_mul_iff_left hpk_ne] at hcoeff
      exact_mod_cast hcoeff
    -- Step 5: Branch on `g.natDegree`. If `0`, `g = g' = 1` and both
    -- conclusions follow directly from `hprod`, `hprod'`.
    by_cases hd : g.natDegree = 0
    · have hg_eq : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg hd
      have hg'_eq : g' = 1 :=
        Polynomial.eq_one_of_monic_natDegree_zero hg' (hdeg ▸ hd)
      refine ⟨by rw [hg_eq, hg'_eq], ?_⟩
      have hg_map : g.map (Int.castRingHom (ZMod (p ^ (k + 1)))) = 1 := by
        rw [hg_eq]; simp
      have hg'_map : g'.map (Int.castRingHom (ZMod (p ^ (k + 1)))) = 1 := by
        rw [hg'_eq]; simp
      rw [hg_map, one_mul] at hprod
      rw [hg'_map, one_mul] at hprod'
      rw [hprod, ← hprod']
    · -- Step 6: Apply coprime cancellation in `Polynomial (ZMod p)`.
      have hg_monic_p : (g.map (Int.castRingHom (ZMod p))).Monic := hg.map _
      have hd_g_map :
          (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree :=
        hg.natDegree_map _
      -- `A.natDegree < g.natDegree`: use `A.natDegree = (g - g').natDegree`
      -- and `(g - g').natDegree < g.natDegree` since `g`, `g'` are monic of the same degree.
      have hpk_ne_int : ((p ^ k : ℕ) : ℤ) ≠ 0 := by
        have hp_pos : 0 < p := (Fact.out (p := Nat.Prime p)).pos
        exact_mod_cast pow_ne_zero k hp_pos.ne'
      have hA_natDegree : A.natDegree = (g - g').natDegree := by
        rw [hA, Polynomial.natDegree_C_mul hpk_ne_int]
      have hsub_lt : (g - g').natDegree < g.natDegree := by
        have hgm : Polynomial.IsMonicOfDegree g g.natDegree := ⟨rfl, hg⟩
        have hg'm : Polynomial.IsMonicOfDegree g' g.natDegree := ⟨hdeg.symm, hg'⟩
        exact hgm.natDegree_sub_lt hd hg'm
      have hA_lt : A.natDegree < g.natDegree := hA_natDegree ▸ hsub_lt
      have hA_map_lt :
          (A.map (Int.castRingHom (ZMod p))).natDegree <
            (g.map (Int.castRingHom (ZMod p))).natDegree := by
        calc (A.map (Int.castRingHom (ZMod p))).natDegree
            ≤ A.natDegree := Polynomial.natDegree_map_le
          _ < g.natDegree := hA_lt
          _ = _ := hd_g_map.symm
      -- Form the cancellation equation `a*h + b*g = 0` after substituting `g'` for `g` via `hg1`.
      have hheq :
          (A.map (Int.castRingHom (ZMod p))) *
              (h.map (Int.castRingHom (ZMod p))) +
            (B.map (Int.castRingHom (ZMod p))) *
              (g.map (Int.castRingHom (ZMod p))) = 0 := by
        have hk := hkey_modp
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          ← hg1] at hk
        linear_combination hk
      obtain ⟨hA_zero, hB_zero⟩ :=
        isCoprime_cancel_of_natDegree_lt hg_monic_p hcop hheq hA_map_lt
      -- Step 7: Lift `A.map φ_p = 0` and `B.map φ_p = 0` back to level `p^(k+1)`.
      refine ⟨?_, ?_⟩
      · have h1 := map_C_pow_mul_eq_zero_of_map_modP_eq_zero (k := k) A hA_zero
        rw [← hA, Polynomial.map_sub, sub_eq_zero] at h1
        exact h1
      · have h1 := map_C_pow_mul_eq_zero_of_map_modP_eq_zero (k := k) B hB_zero
        rw [← hB, Polynomial.map_sub, sub_eq_zero] at h1
        exact h1

/--
Quadratic lifting is compatible with the Mathlib uniqueness theorem at the
doubled prime-power precision.
-/
theorem quadraticHenselStep_unique_mod_pow_two_mul
    (f g h s t : Hex.ZPoly) (g' h' : Polynomial ℤ)
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    (hk : 0 < k)
    (hprod : Hex.ZPoly.congr (g * h) f (p ^ k))
    (hbez : Hex.ZPoly.congr (s * g + t * h) 1 (p ^ k))
    (hmonic : Hex.DensePoly.Monic g)
    (hg' : g'.Monic)
    (hdeg :
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).natDegree =
        g'.natDegree)
    (hprod' :
      let φ := Int.castRingHom (ZMod (p ^ (2 * k)))
      (g'.map φ) * (h'.map φ) =
        (HexPolyMathlib.toPolynomial f).map φ)
    (hg1 :
      let φ := Int.castRingHom (ZMod p)
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).map φ =
        g'.map φ)
    (hh1 :
      let φ := Int.castRingHom (ZMod p)
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).h).map φ =
        h'.map φ)
    (hcop :
      let φ := Int.castRingHom (ZMod p)
      IsCoprime
        ((HexPolyMathlib.toPolynomial
          (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).map φ)
        ((HexPolyMathlib.toPolynomial
          (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).h).map φ)) :
    let r := Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t
    let φ := Int.castRingHom (ZMod (p ^ (2 * k)))
    (HexPolyMathlib.toPolynomial r.g).map φ = g'.map φ ∧
      (HexPolyMathlib.toPolynomial r.h).map φ = h'.map φ := by
  -- The quadratic step doubles precision from its modulus `m = p^k` to
  -- `m * m = p^(2*k)`, so this is a specialisation of `hensel_unique` at level
  -- `2 * k`. The substrate hypotheses pass through directly; monicity comes from
  -- `quadraticHenselStep_monic` and the product equality from
  -- `quadraticHenselStep_factor_correct`, after bridging `p^k * p^k = p^(2*k)`.
  have hprime : Nat.Prime p := Fact.out
  have hm_pos : 0 < p ^ k := pow_pos hprime.pos k
  have hpk_gt1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hprime.one_lt
  have hg_monic :
      (HexPolyMathlib.toPolynomial
        (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).Monic :=
    quadraticHenselStep_monic (p ^ k) f g h s t hpk_gt1 hmonic
  have hmm : p ^ k * p ^ k = p ^ (2 * k) := by rw [two_mul, pow_add]
  have hprod_2k :
      let φ := Int.castRingHom (ZMod (p ^ (2 * k)))
      (HexPolyMathlib.toPolynomial
            (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g).map φ *
          (HexPolyMathlib.toPolynomial
            (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).h).map φ =
        (HexPolyMathlib.toPolynomial f).map φ := by
    have hfc :=
      quadraticHenselStep_factor_correct (p ^ k) f g h s t hm_pos hprod hbez hmonic
    simp only at hfc ⊢
    exact hmm ▸ hfc
  exact hensel_unique
    (HexPolyMathlib.toPolynomial f)
    (HexPolyMathlib.toPolynomial (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).g)
    (HexPolyMathlib.toPolynomial (Hex.ZPoly.quadraticHenselStep (p ^ k) f g h s t).h)
    g' h' p (2 * k) (by omega) hg_monic hg' hdeg hprod_2k hprod' hg1 hh1 hcop

/--
The recursive linear multifactor invariant supplies enough mod-`p` split data
to initialise the quadratic multifactor invariant, provided the raw input heads
are monic.

The helper is stated for a target `f'` congruent to the linear target `f` modulo
`p`: recursively, the linear and quadratic lifted cofactors are not equal, but
both remain congruent modulo the base prime to the same raw complementary
product.
-/
private theorem quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant_congr
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (f f' : Hex.ZPoly) (factors : List Hex.ZPoly)
    (hk : 1 ≤ k)
    (hmonic : ∀ g ∈ factors, Hex.DensePoly.Monic g)
    (htarget : Hex.ZPoly.congr f f' p)
    (hnonempty : factors ≠ [])
    (hinv : Hex.ZPoly.MultifactorLiftInvariant p k f factors) :
    Hex.ZPoly.QuadraticMultifactorLiftInvariant p k f' factors := by
  induction factors generalizing f f' with
  | nil =>
      exact (hnonempty rfl).elim
  | cons g rest ih =>
      cases rest with
      | nil =>
          simp [Hex.ZPoly.QuadraticMultifactorLiftInvariant]
      | cons h tail =>
          let restFactors : Array Hex.ZPoly := (h :: tail).toArray
          let splitProduct : Hex.ZPoly := Array.polyProduct restFactors
          let xgcd := Hex.ZPoly.normalizedXGCD p g splitProduct
          let s : Hex.ZPoly := Hex.FpPoly.liftToZ xgcd.left
          let t : Hex.ZPoly := Hex.FpPoly.liftToZ xgcd.right
          let linearLifted :=
            Hex.ZPoly.henselLift p k f g splitProduct xgcd.left xgcd.right
          let quadraticLifted :=
            Hex.ZPoly.henselLiftQuadratic p k f' g splitProduct s t
          rcases hinv with ⟨hstart, _hstepDegree, _hstepBezout, htail⟩
          have hstart' :
              Hex.ZPoly.LinearLiftLoopInvariant p 1 f xgcd.left xgcd.right
                { g := Hex.ZPoly.reduceModPow g p 1
                  h := Hex.ZPoly.reduceModPow splitProduct p 1 } := by
            simpa [restFactors, splitProduct, xgcd] using hstart
          have hprod_reduced :
              Hex.ZPoly.congr
                (Hex.ZPoly.reduceModPow g p 1 *
                  Hex.ZPoly.reduceModPow splitProduct p 1) f p := by
            simpa [Nat.pow_one] using hstart'.1
          have hreduce_prod :
              Hex.ZPoly.congr
                (Hex.ZPoly.reduceModPow g p 1 *
                  Hex.ZPoly.reduceModPow splitProduct p 1)
                (g * splitProduct) p := by
            apply Hex.ZPoly.congr_mul
            · have hg :=
                Hex.ZPoly.congr_reduceModPow g p 1
                  (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
              simpa [Nat.pow_one] using hg
            · have hh :=
                Hex.ZPoly.congr_reduceModPow splitProduct p 1
                  (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
              simpa [Nat.pow_one] using hh
          have hprod_raw_f :
              Hex.ZPoly.congr (g * splitProduct) f p :=
            Hex.ZPoly.congr_trans _ _ _ p
              (Hex.ZPoly.congr_symm _ _ _ hreduce_prod) hprod_reduced
          have hprod_raw :
              Hex.ZPoly.congr (g * splitProduct) f' p :=
            Hex.ZPoly.congr_trans _ _ _ p hprod_raw_f htarget
          have hbez_reduced :
              Hex.ZPoly.congr
                (Hex.FpPoly.liftToZ
                  (xgcd.left * Hex.ZPoly.modP p g +
                    xgcd.right * Hex.ZPoly.modP p splitProduct)) 1 p := by
            simpa [Hex.ZPoly.modP_reduceModPow_of_pos p 1 g (by omega),
              Hex.ZPoly.modP_reduceModPow_of_pos p 1 splitProduct (by omega)]
              using hstart'.2.1
          have hbez_lift :
              Hex.ZPoly.congr
                (Hex.FpPoly.liftToZ
                  (xgcd.left * Hex.ZPoly.modP p g +
                    xgcd.right * Hex.ZPoly.modP p splitProduct))
                (s * g + t * splitProduct) p := by
            apply Hex.ZPoly.congr_liftToZ_of_modP_eq
            simp [s, t]
          have hbez :
              Hex.ZPoly.congr (s * g + t * splitProduct) 1 p :=
            Hex.ZPoly.congr_trans _ _ _ p
              (Hex.ZPoly.congr_symm _ _ _ hbez_lift) hbez_reduced
          have hg_monic : Hex.DensePoly.Monic g := by
            exact hmonic g (by simp)
          have hquad_start :
              Hex.ZPoly.QuadraticLiftLoopInvariant p f'
                { g := g, h := splitProduct, s := s, t := t } :=
            Hex.ZPoly.QuadraticLiftLoopInvariant.of_product_bezout_monic
              hprod_raw hbez hg_monic
          have hlinear_h :
              Hex.ZPoly.congr linearLifted.h splitProduct p := by
            simpa [linearLifted, splitProduct, xgcd] using
              Hex.ZPoly.henselLift_h_congr_mod_base
                p k f g splitProduct xgcd.left xgcd.right hk
          have hquadratic_h :
              Hex.ZPoly.congr quadraticLifted.h splitProduct p := by
            simpa [quadraticLifted, splitProduct, xgcd, s, t] using
              Hex.ZPoly.henselLiftQuadratic_h_congr_mod_base
                p k f' g splitProduct s t hk (Fact.out (p := Nat.Prime p)).one_lt
                hquad_start
          have htail_target :
              Hex.ZPoly.congr linearLifted.h quadraticLifted.h p :=
            Hex.ZPoly.congr_trans _ _ _ p hlinear_h
              (Hex.ZPoly.congr_symm _ _ _ hquadratic_h)
          have htail_monic :
              ∀ q ∈ (h :: tail), Hex.DensePoly.Monic q := by
            intro q hq
            exact hmonic q (by simp [hq])
          have htail' :
              Hex.ZPoly.MultifactorLiftInvariant p k linearLifted.h (h :: tail) := by
            simpa [linearLifted, restFactors, splitProduct, xgcd] using htail
          have hquad_tail :
              Hex.ZPoly.QuadraticMultifactorLiftInvariant p k
                quadraticLifted.h (h :: tail) :=
            ih linearLifted.h quadraticLifted.h htail_monic htail_target
              (by simp) htail'
          exact ⟨by simpa [restFactors, splitProduct, xgcd, s, t] using hquad_start,
            by simpa [quadraticLifted, restFactors, splitProduct, xgcd, s, t]
              using hquad_tail⟩

/--
The linear multifactor invariant can initialise the quadratic multifactor
invariant when every raw input head is monic.
-/
theorem quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (f : Hex.ZPoly) (factors : List Hex.ZPoly)
    (hk : 1 ≤ k)
    (hmonic : ∀ g ∈ factors, Hex.DensePoly.Monic g)
    (hinv : Hex.ZPoly.MultifactorLiftInvariant p k f factors) :
    Hex.ZPoly.QuadraticMultifactorLiftInvariant p k f factors := by
  cases factors with
  | nil =>
      simpa [Hex.ZPoly.QuadraticMultifactorLiftInvariant] using hinv
  | cons g rest =>
      exact
        quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant_congr
          p k f f (g :: rest) hk hmonic (Hex.ZPoly.congr_refl f p)
          (by simp) hinv

/--
List-level agreement of the linear and quadratic multifactor lifters over
congruent targets, after canonical reduction modulo `p ^ k`.

The targets `f` (linear) and `f'` (quadratic) are taken congruent modulo
`p ^ k` rather than only modulo `p`: at each non-singleton split,
`hensel_unique` equates the two lifted heads *and* the two lifted complements
modulo `p ^ k`, and the complement equality is exactly the recursive target
congruence consumed by the inductive call. Mod-`p` target congruence is enough
to transport the *invariant* (see
`quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant_congr`), but it
is not enough to pin the *lifted factors* modulo `p ^ k`, since Hensel lifting
is target-dependent above the base prime. The public theorem instantiates this
helper at `f' = f` via `Hex.ZPoly.congr_refl`.
-/
private theorem multifactorLiftList_map_eq_quadratic
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (f f' : Hex.ZPoly) (factors : List Hex.ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hmonic : ∀ g ∈ factors, Hex.DensePoly.Monic g)
    (htarget : Hex.ZPoly.congr f f' (p ^ k))
    (hinv : Hex.ZPoly.MultifactorLiftInvariant p k f factors) :
    (Hex.ZPoly.multifactorLiftList p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map (Int.castRingHom (ZMod (p ^ k)))) =
      (Hex.ZPoly.multifactorLiftQuadraticList p k f' factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map (Int.castRingHom (ZMod (p ^ k)))) := by
  induction factors generalizing f f' with
  | nil =>
      simp [Hex.ZPoly.multifactorLiftList, Hex.ZPoly.multifactorLiftQuadraticList]
  | cons g rest ih =>
      cases rest with
      | nil =>
          have hcongr :
              Hex.ZPoly.congr (Hex.ZPoly.reduceModPow f p k)
                (Hex.ZPoly.reduceModPow f' p k) (p ^ k) := by
            have hf := Hex.ZPoly.congr_reduceModPow f p k
              (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
            have hf' := Hex.ZPoly.congr_reduceModPow f' p k
              (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
            exact Hex.ZPoly.congr_trans _ _ _ (p ^ k) hf
              (Hex.ZPoly.congr_trans _ _ _ (p ^ k) htarget
                (Hex.ZPoly.congr_symm _ _ _ hf'))
          have hmap := zpoly_congr_toPolynomial_map_eq
            (Hex.ZPoly.reduceModPow f p k) (Hex.ZPoly.reduceModPow f' p k) (p ^ k) hcongr
          simpa [Hex.ZPoly.multifactorLiftList, Hex.ZPoly.multifactorLiftQuadraticList]
            using hmap
      | cons h tail =>
          rcases hinv with ⟨hstart, hstepDeg, hstepBez, htail⟩
          let restFactors : Array Hex.ZPoly := (h :: tail).toArray
          let splitProduct : Hex.ZPoly := Array.polyProduct restFactors
          let xgcd := Hex.ZPoly.normalizedXGCD p g splitProduct
          let s : Hex.ZPoly := Hex.FpPoly.liftToZ xgcd.left
          let t : Hex.ZPoly := Hex.FpPoly.liftToZ xgcd.right
          let linearLifted := Hex.ZPoly.henselLift p k f g splitProduct xgcd.left xgcd.right
          let quadraticLifted := Hex.ZPoly.henselLiftQuadratic p k f' g splitProduct s t
          -- Align the destructured invariant pieces with the local abbreviations.
          have hstart' :
              Hex.ZPoly.LinearLiftLoopInvariant p 1 f xgcd.left xgcd.right
                { g := Hex.ZPoly.reduceModPow g p 1
                  h := Hex.ZPoly.reduceModPow splitProduct p 1 } := hstart
          -- Linear product spec modulo `p ^ k`.
          have hlin_prod :
              Hex.ZPoly.congr (linearLifted.g * linearLifted.h) f (p ^ k) :=
            Hex.ZPoly.henselLift_spec p k f g splitProduct xgcd.left xgcd.right hk hp
              hstart' hstepDeg hstepBez
          have hlin_g_monic : Hex.DensePoly.Monic linearLifted.g :=
            Hex.ZPoly.henselLift_monic p k f g splitProduct xgcd.left xgcd.right hk hp
              hstart' hstepDeg hstepBez
          -- Rebuild the quadratic loop-start from the linear loop-start, the
          -- raw-product/Bezout congruences mod `p`, and raw head monicity.
          have htarget_p : Hex.ZPoly.congr f f' p := by
            have h := Hex.ZPoly.congr_pow_of_le p 1 k f f' hk htarget
            simpa [Nat.pow_one] using h
          have hprod_reduced :
              Hex.ZPoly.congr
                (Hex.ZPoly.reduceModPow g p 1 *
                  Hex.ZPoly.reduceModPow splitProduct p 1) f p := by
            simpa [Nat.pow_one] using hstart'.1
          have hreduce_prod :
              Hex.ZPoly.congr
                (Hex.ZPoly.reduceModPow g p 1 *
                  Hex.ZPoly.reduceModPow splitProduct p 1)
                (g * splitProduct) p := by
            apply Hex.ZPoly.congr_mul
            · have hg :=
                Hex.ZPoly.congr_reduceModPow g p 1
                  (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
              simpa [Nat.pow_one] using hg
            · have hh :=
                Hex.ZPoly.congr_reduceModPow splitProduct p 1
                  (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
              simpa [Nat.pow_one] using hh
          have hprod_raw_f :
              Hex.ZPoly.congr (g * splitProduct) f p :=
            Hex.ZPoly.congr_trans _ _ _ p
              (Hex.ZPoly.congr_symm _ _ _ hreduce_prod) hprod_reduced
          have hprod_raw :
              Hex.ZPoly.congr (g * splitProduct) f' p :=
            Hex.ZPoly.congr_trans _ _ _ p hprod_raw_f htarget_p
          have hbez_reduced :
              Hex.ZPoly.congr
                (Hex.FpPoly.liftToZ
                  (xgcd.left * Hex.ZPoly.modP p g +
                    xgcd.right * Hex.ZPoly.modP p splitProduct)) 1 p := by
            simpa [Hex.ZPoly.modP_reduceModPow_of_pos p 1 g (by omega),
              Hex.ZPoly.modP_reduceModPow_of_pos p 1 splitProduct (by omega)]
              using hstart'.2.1
          have hbez_lift :
              Hex.ZPoly.congr
                (Hex.FpPoly.liftToZ
                  (xgcd.left * Hex.ZPoly.modP p g +
                    xgcd.right * Hex.ZPoly.modP p splitProduct))
                (s * g + t * splitProduct) p := by
            apply Hex.ZPoly.congr_liftToZ_of_modP_eq
            simp [s, t]
          have hbez :
              Hex.ZPoly.congr (s * g + t * splitProduct) 1 p :=
            Hex.ZPoly.congr_trans _ _ _ p
              (Hex.ZPoly.congr_symm _ _ _ hbez_lift) hbez_reduced
          have hg_monic : Hex.DensePoly.Monic g := hmonic g (by simp)
          have hquad_start :
              Hex.ZPoly.QuadraticLiftLoopInvariant p f'
                { g := g, h := splitProduct, s := s, t := t } :=
            Hex.ZPoly.QuadraticLiftLoopInvariant.of_product_bezout_monic
              hprod_raw hbez hg_monic
          -- Quadratic product spec modulo `p ^ k`.
          have hquad_prod :
              Hex.ZPoly.congr (quadraticLifted.g * quadraticLifted.h) f' (p ^ k) :=
            Hex.ZPoly.henselLiftQuadratic_spec p k f' g splitProduct s t hk hp hquad_start
          have hquad_g_monic : Hex.DensePoly.Monic quadraticLifted.g :=
            Hex.ZPoly.henselLiftQuadratic_g_monic p k f' g splitProduct s t hk hp hquad_start
          -- Base-prime agreement of the lifted heads and complements.
          have hlin_g_base : Hex.ZPoly.congr linearLifted.g g p :=
            Hex.ZPoly.henselLift_g_congr_mod_base p k f g splitProduct
              xgcd.left xgcd.right hk
          have hlin_h_base : Hex.ZPoly.congr linearLifted.h splitProduct p :=
            Hex.ZPoly.henselLift_h_congr_mod_base p k f g splitProduct
              xgcd.left xgcd.right hk
          have hquad_g_base : Hex.ZPoly.congr quadraticLifted.g g p :=
            Hex.ZPoly.henselLiftQuadratic_g_congr_mod_base p k f' g splitProduct s t hk hp
              hquad_start
          have hquad_h_base : Hex.ZPoly.congr quadraticLifted.h splitProduct p :=
            Hex.ZPoly.henselLiftQuadratic_h_congr_mod_base p k f' g splitProduct s t hk hp
              hquad_start
          -- Mathlib-side hypotheses for `hensel_unique`.
          have hg : (HexPolyMathlib.toPolynomial linearLifted.g).Monic :=
            toPolynomial_monic_of_dense_monic _ hlin_g_monic
          have hg' : (HexPolyMathlib.toPolynomial quadraticLifted.g).Monic :=
            toPolynomial_monic_of_dense_monic _ hquad_g_monic
          have hg1 :
              (HexPolyMathlib.toPolynomial linearLifted.g).map (Int.castRingHom (ZMod p)) =
                (HexPolyMathlib.toPolynomial quadraticLifted.g).map (Int.castRingHom (ZMod p)) :=
            zpoly_congr_toPolynomial_map_eq _ _ p
              (Hex.ZPoly.congr_trans _ _ _ p hlin_g_base
                (Hex.ZPoly.congr_symm _ _ _ hquad_g_base))
          have hh1 :
              (HexPolyMathlib.toPolynomial linearLifted.h).map (Int.castRingHom (ZMod p)) =
                (HexPolyMathlib.toPolynomial quadraticLifted.h).map (Int.castRingHom (ZMod p)) :=
            zpoly_congr_toPolynomial_map_eq _ _ p
              (Hex.ZPoly.congr_trans _ _ _ p hlin_h_base
                (Hex.ZPoly.congr_symm _ _ _ hquad_h_base))
          have hdeg :
              (HexPolyMathlib.toPolynomial linearLifted.g).natDegree =
                (HexPolyMathlib.toPolynomial quadraticLifted.g).natDegree :=
            natDegree_eq_of_monic_map_eq p hg hg' hg1
          have hprod :
              (HexPolyMathlib.toPolynomial linearLifted.g).map (Int.castRingHom (ZMod (p ^ k))) *
                  (HexPolyMathlib.toPolynomial linearLifted.h).map
                    (Int.castRingHom (ZMod (p ^ k))) =
                (HexPolyMathlib.toPolynomial f).map (Int.castRingHom (ZMod (p ^ k))) := by
            have hmap := zpoly_congr_toPolynomial_map_eq
              (linearLifted.g * linearLifted.h) f (p ^ k) hlin_prod
            simpa [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul] using hmap
          have hprod' :
              (HexPolyMathlib.toPolynomial quadraticLifted.g).map (Int.castRingHom (ZMod (p ^ k))) *
                  (HexPolyMathlib.toPolynomial quadraticLifted.h).map
                    (Int.castRingHom (ZMod (p ^ k))) =
                (HexPolyMathlib.toPolynomial f).map (Int.castRingHom (ZMod (p ^ k))) := by
            have hmap := zpoly_congr_toPolynomial_map_eq
              (quadraticLifted.g * quadraticLifted.h) f' (p ^ k) hquad_prod
            have htgt := zpoly_congr_toPolynomial_map_eq f f' (p ^ k) htarget
            simp only [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul] at hmap
            simp only at htgt
            rw [hmap]; exact htgt.symm
          have hcop :
              IsCoprime
                ((HexPolyMathlib.toPolynomial linearLifted.g).map (Int.castRingHom (ZMod p)))
                ((HexPolyMathlib.toPolynomial linearLifted.h).map (Int.castRingHom (ZMod p))) := by
            have hbase := isCoprime_of_zpoly_bezout p g splitProduct s t hbez
            have hgp : (HexPolyMathlib.toPolynomial linearLifted.g).map
                (Int.castRingHom (ZMod p)) =
                (HexPolyMathlib.toPolynomial g).map (Int.castRingHom (ZMod p)) :=
              zpoly_congr_toPolynomial_map_eq _ _ p hlin_g_base
            have hhp : (HexPolyMathlib.toPolynomial linearLifted.h).map
                (Int.castRingHom (ZMod p)) =
                (HexPolyMathlib.toPolynomial splitProduct).map (Int.castRingHom (ZMod p)) :=
              zpoly_congr_toPolynomial_map_eq _ _ p hlin_h_base
            rw [hgp, hhp]; exact hbase
          obtain ⟨hgeq, hheq⟩ := hensel_unique
            (HexPolyMathlib.toPolynomial f)
            (HexPolyMathlib.toPolynomial linearLifted.g)
            (HexPolyMathlib.toPolynomial linearLifted.h)
            (HexPolyMathlib.toPolynomial quadraticLifted.g)
            (HexPolyMathlib.toPolynomial quadraticLifted.h)
            p k (by omega) hg hg' hdeg hprod hprod' hg1 hh1 hcop
          -- Recurse on the lifted complements, congruent modulo `p ^ k`.
          have htarget' : Hex.ZPoly.congr linearLifted.h quadraticLifted.h (p ^ k) :=
            zpoly_congr_of_toPolynomial_map_eq linearLifted.h quadraticLifted.h (p ^ k) hheq
          have hmonic' : ∀ q ∈ (h :: tail), Hex.DensePoly.Monic q :=
            fun q hq => hmonic q (by simp [hq])
          have hinv' :
              Hex.ZPoly.MultifactorLiftInvariant p k linearLifted.h (h :: tail) := htail
          have hexpandL :
              (Hex.ZPoly.multifactorLiftList p k f (g :: h :: tail)).toList =
                linearLifted.g ::
                  (Hex.ZPoly.multifactorLiftList p k linearLifted.h (h :: tail)).toList := by
            simp [Hex.ZPoly.multifactorLiftList, restFactors, splitProduct, xgcd, linearLifted]
          have hexpandQ :
              (Hex.ZPoly.multifactorLiftQuadraticList p k f' (g :: h :: tail)).toList =
                quadraticLifted.g ::
                  (Hex.ZPoly.multifactorLiftQuadraticList p k quadraticLifted.h
                    (h :: tail)).toList := by
            simp [Hex.ZPoly.multifactorLiftQuadraticList, restFactors, splitProduct, xgcd, s, t,
              quadraticLifted]
          rw [hexpandL, hexpandQ, List.map_cons, List.map_cons]
          refine List.cons_eq_cons.mpr ⟨hgeq, ?_⟩
          exact ih linearLifted.h quadraticLifted.h hmonic' htarget' hinv'

/--
The linear and quadratic multifactor lifters agree modulo `p ^ k` after
canonical reduction, when both are applied to the same input under the
recursive `MultifactorLiftInvariant` precondition consumed by both
`Hex.ZPoly.multifactorLift_spec` and
`Hex.ZPoly.multifactorLiftQuadratic_spec`.

The result is stated over the public array/product multifactor surface
rather than the private split-tree helpers, and is expressed in Mathlib
form via `Polynomial.map (Int.castRingHom (ZMod (p ^ k)))`. Through
`zpoly_congr_toPolynomial_map_eq` / `zpoly_congr_of_toPolynomial_map_eq`,
this is equivalent to per-factor canonicalisation by
`Hex.ZPoly.reduceModPow _ p k`.

The raw-head monicity hypothesis `hmonic` is required: it pins each split
head's Mathlib degree so `hensel_unique` can identify the linear and
quadratic lifts. See `multifactorLiftList_map_eq_quadratic` for the
congruent-target induction behind the proof.

This is the lift-uniqueness obligation that `hex-hensel` defers to
`hex-hensel-mathlib`; see `SPEC/Libraries/hex-hensel.md` and the
companion-statement note at the top of `HexHensel/QuadraticMultifactor.lean`.
-/
theorem multifactorLift_eq_multifactorLiftQuadratic
    (p k : Nat) [Fact (Nat.Prime p)] [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (f : Hex.ZPoly) (factors : Array Hex.ZPoly)
    (hk : 1 ≤ k)
    (hp : 1 < p)
    (hmonic : ∀ g ∈ factors.toList, Hex.DensePoly.Monic g)
    (hinv : Hex.ZPoly.MultifactorLiftInvariant p k f factors.toList) :
    let φ := Int.castRingHom (ZMod (p ^ k))
    (Hex.ZPoly.multifactorLift p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map φ) =
      (Hex.ZPoly.multifactorLiftQuadratic p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map φ) := by
  intro _φ
  exact multifactorLiftList_map_eq_quadratic p k f f factors.toList hk hp hmonic
    (Hex.ZPoly.congr_refl f (p ^ k)) hinv

end

end HexHenselMathlib
