/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

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

section BalancedBridgeHelpers
open Hex Hex.ZPoly

/-- `a⁻¹ ≠ 0` for a nonzero field element `a : ZMod64 p`. -/
private theorem zmod64_inv_ne_zero {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    {a : ZMod64 p} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  intro ha0
  have h1 : a * a⁻¹ = 1 := ZMod64.mul_inv_eq_one_of_ne_zero ha
  rw [ha0, ZMod64.mul_zero] at h1
  exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h1.symm

/-- The normalised XGCD gcd is `1` whenever every common divisor of the two
`modP` images divides the unit polynomial. This is the coprimality-side entry
to the split Bezout data, dual to the squarefree-side `gcd² ∣ X` argument used by
the recombination discharger. -/
private theorem normalizedXGCD_gcd_eq_one_of_common_dvd_one
    (p : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p] (g h : ZPoly)
    (hcommon : ∀ e : FpPoly p, e ∣ ZPoly.modP p g → e ∣ ZPoly.modP p h → e ∣ (1 : FpPoly p)) :
    (normalizedXGCD p g h).gcd = 1 := by
  have h1ne : (1 : FpPoly p) ≠ 0 := by
    intro hh
    have hcoeff : (DensePoly.C (1 : ZMod64 p) : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 := by
      rw [show (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 from rfl, hh]
    rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
    simp only [if_true] at hcoeff
    exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) hcoeff
  have hr_dvd_one : DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h) ∣ (1 : FpPoly p) :=
    hcommon _ (DensePoly.gcd_dvd_left _ _) (DensePoly.gcd_dvd_right _ _)
  have hr_ne : DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h) ≠ 0 := by
    intro hz; rw [hz] at hr_dvd_one; obtain ⟨u, hu⟩ := hr_dvd_one
    rw [FpPoly.zero_mul] at hu; exact h1ne hu
  have hsize_pos : 0 < DensePoly.size (DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h)) :=
    FpPoly.size_pos_of_ne_zero hr_ne
  have hlc_ne : DensePoly.leadingCoeff (DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h))
      ≠ (0 : ZMod64 p) := by
    rw [DensePoly.leadingCoeff_eq_coeff_last _ hsize_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size _ hsize_pos
  have hinv_ne :
      (DensePoly.leadingCoeff (DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h)))⁻¹ ≠ 0 :=
    zmod64_inv_ne_zero hlc_ne
  have hshape : (normalizedXGCD p g h).gcd
      = DensePoly.scale (DensePoly.leadingCoeff (DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h)))⁻¹
          (DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h)) := by
    show DensePoly.scale (DensePoly.leadingCoeff (DensePoly.xgcd (ZPoly.modP p g) (ZPoly.modP p h)).gcd)⁻¹
        (DensePoly.xgcd (ZPoly.modP p g) (ZPoly.modP p h)).gcd = _
    rw [DensePoly.gcd_eq_xgcd_gcd]
  rw [hshape]
  apply FpPoly.eq_one_of_monic_dvd_one
  · unfold DensePoly.Monic
    rw [FpPoly.leadingCoeff_scale_of_ne_zero_of_nonzero hinv_ne _
      (Nat.pos_iff_ne_zero.mp hsize_pos)]
    exact ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hlc_ne
  · obtain ⟨q1, hq1⟩ := FpPoly.dvd_scale_self_of_ne_zero hinv_ne
      (DensePoly.gcd (ZPoly.modP p g) (ZPoly.modP p h))
    obtain ⟨q2, hq2⟩ := hr_dvd_one
    exact ⟨q1 * q2, by rw [← FpPoly.mul_assoc, ← hq1, ← hq2]⟩

/-- Balanced split coprimality over `ZPoly`, stated directly on the integer
polynomials (via their `modP` images) rather than on the `FpPoly` factors. This
is the `ZPoly`-level analogue of `QuadraticMultifactorCoprimeSplits` used to
transport arbitrary monic factor lists (as arise in the linear/quadratic
agreement) into the balanced quadratic invariant. -/
def ZCoprimeSplits (p : Nat) [ZMod64.Bounds p] : List ZPoly → Prop
  | [] => True
  | [_g] => True
  | g₀ :: g₁ :: rest =>
      let gs := g₀ :: g₁ :: rest
      let half := gs.length / 2
      let L := gs.take half
      let R := gs.drop half
      (normalizedXGCD p (Array.polyProduct L.toArray) (Array.polyProduct R.toArray)).gcd
          = (1 : FpPoly p) ∧ ZCoprimeSplits p L ∧ ZCoprimeSplits p R
  termination_by factors => factors.length
  decreasing_by all_goals (simp only [List.length_take, List.length_drop, List.length_cons]; omega)

/-- Build the balanced quadratic multifactor lift invariant from `ZPoly`-level
boundary facts: monic factors, split coprimality (`ZCoprimeSplits`), and the
lifted product congruence modulo `p`. No monic-target hypothesis is required —
the balanced invariant constrains only the leading factor of each split, which
is a product of the (monic) input factors. -/
theorem inv_of_ZCoprimeSplits (p k : Nat) [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : ZPoly) (factors : List ZPoly) (hp : 1 < p) (hk : 1 ≤ k)
    (hfactors_monic : ∀ g ∈ factors, DensePoly.Monic g)
    (hproduct : ZPoly.congr (Array.polyProduct factors.toArray) f p)
    (hcop : ZCoprimeSplits p factors) (hne : factors ≠ []) :
    QuadraticMultifactorLiftInvariant p k f factors := by
  induction factors using ZCoprimeSplits.induct generalizing f with
  | case1 => exact absurd rfl hne
  | case2 g => simp [QuadraticMultifactorLiftInvariant]
  | case3 g₀ g₁ rest gs half L R ihL ihR =>
      simp only [ZCoprimeSplits] at hcop
      obtain ⟨hgcd, hcopL, hcopR⟩ := hcop
      rw [QuadraticMultifactorLiftInvariant]
      have hLmonic : ∀ x ∈ (List.take ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)),
          DensePoly.Monic x := fun x hx => hfactors_monic x (List.mem_of_mem_take hx)
      have hRmonic : ∀ x ∈ (List.drop ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)),
          DensePoly.Monic x := fun x hx => hfactors_monic x (List.mem_of_mem_drop hx)
      have hprod : ZPoly.congr
          (Array.polyProduct (List.take ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)).toArray *
            Array.polyProduct (List.drop ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)).toArray)
          f p := by
        rw [← polyProduct_append,
          show ((List.take ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)).toArray ++
                (List.drop ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)).toArray)
              = ((List.take ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest) ++
                 List.drop ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest)).toArray) from by simp,
          List.take_append_drop]
        exact hproduct
      have hbez := normalizedXGCD_liftToZ_bezout_congr_of_gcd_eq_one p _ _ hgcd
      have hstart := QuadraticLiftLoopInvariant.of_product_bezout_monic hprod hbez
        (monic_polyProduct_toArray _ hLmonic)
      refine ⟨hstart, ?_, ?_⟩
      · refine ihL _ hLmonic
          (ZPoly.congr_symm _ _ _
            (henselLiftQuadratic_g_congr_mod_base p k f _ _ _ _ hk hp hstart)) hcopL ?_
        show List.take ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest) ≠ []
        apply List.ne_nil_of_length_pos
        simp only [List.length_take, List.length_cons]; omega
      · refine ihR _ hRmonic
          (ZPoly.congr_symm _ _ _
            (henselLiftQuadratic_h_congr_mod_base p k f _ _ _ _ hk hp hstart)) hcopR ?_
        show List.drop ((g₀ :: g₁ :: rest).length / 2) (g₀ :: g₁ :: rest) ≠ []
        apply List.ne_nil_of_length_pos
        simp only [List.length_drop, List.length_cons]; omega

end BalancedBridgeHelpers

section LinearToZCoprimeBridge
open Hex Hex.ZPoly

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

/-- Target-free common-divisor coprimality of two `FpPoly p` elements: every
common divisor of `a` and `b` divides the unit polynomial. This is the
squarefree-free coprimality carrier extracted from the linear Bezout data. -/
private def CommonDvdOne (a b : FpPoly p) : Prop :=
  ∀ e : FpPoly p, e ∣ a → e ∣ b → e ∣ (1 : FpPoly p)

omit [ZMod64.PrimeModulus p] in
private theorem CommonDvdOne.symm {a b : FpPoly p} (h : CommonDvdOne a b) :
    CommonDvdOne b a :=
  fun e he_b he_a => h e he_a he_b

omit [ZMod64.PrimeModulus p] in
/-- Transitivity of `FpPoly` divisibility, reconstructed manually because the
`Dvd` instance does not carry a `Trans` chain usable by `calc`/`.trans`. -/
private theorem fp_dvd_trans {a b c : FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  exact ⟨r * s, by rw [hs, hr, FpPoly.mul_assoc]⟩

/-- If `a` is coprime with both `b` and `c`, it is coprime with `b * c`. Local
copy of the private Berlekamp-side `coprime_mul_of_coprime_both`. -/
private theorem CommonDvdOne.mul {a b c : FpPoly p}
    (hab : CommonDvdOne a b) (hac : CommonDvdOne a c) :
    CommonDvdOne a (b * c) := by
  intro e he_a he_bc
  have he_coprime_b : ∀ d : FpPoly p, d ∣ b → d ∣ e → d ∣ (1 : FpPoly p) :=
    fun d hdb hde => hab d (fp_dvd_trans hde he_a) hdb
  have he_c : e ∣ c :=
    FpPoly.dvd_of_dvd_mul_of_common_dvd_one he_bc he_coprime_b
  exact hac e he_a he_c

omit [ZMod64.PrimeModulus p] in
/-- A `liftToZ` value congruent to `1` modulo `p` is the unit `FpPoly`. -/
private theorem fpPoly_eq_one_of_congr_liftToZ (X : FpPoly p)
    (h : ZPoly.congr (FpPoly.liftToZ X) 1 p) : X = 1 := by
  have hmod := modP_eq_of_congr p (FpPoly.liftToZ X) 1 h
  rwa [FpPoly.modP_liftToZ, modP_one] at hmod

omit [ZMod64.PrimeModulus p] in
/-- From a mod-`p` Bezout identity `s * a + t * b = 1` extract the coprimality
carrier `CommonDvdOne a b`. -/
private theorem commonDvdOne_of_bezout {a b s t : FpPoly p}
    (h : s * a + t * b = 1) : CommonDvdOne a b := by
  intro e he_a he_b
  have h1 : e ∣ s * a := DensePoly.dvd_mul_left_poly s he_a
  have h2 : e ∣ t * b := DensePoly.dvd_mul_left_poly t he_b
  have h3 : e ∣ (s * a + t * b) := DensePoly.dvd_add_poly h1 h2
  rwa [h] at h3

/-- Any member of a factor list divides the ordered `Array.polyProduct` of that
list. Local copy of the private Berlekamp-Zassenhaus lemma. -/
private theorem zpoly_dvd_polyProduct {q : ZPoly} :
    ∀ factors : List ZPoly, q ∈ factors → q ∣ Array.polyProduct factors.toArray
  | [], hmem => absurd hmem List.not_mem_nil
  | head :: tail, hmem => by
      rw [ZPoly.polyProduct_cons_toArray]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst q
        exact ⟨Array.polyProduct tail.toArray, rfl⟩
      · rcases zpoly_dvd_polyProduct tail htail with ⟨c, hc⟩
        refine ⟨head * c, ?_⟩
        rw [hc, ← DensePoly.mul_assoc_poly (S := Int) head q c,
          DensePoly.mul_comm_poly (S := Int) head q,
          DensePoly.mul_assoc_poly (S := Int) q head c]

omit [ZMod64.PrimeModulus p] in
/-- `modP` is monotone under `ZPoly` divisibility. -/
private theorem modP_dvd_of_dvd {a P : ZPoly} (h : a ∣ P) :
    modP p a ∣ modP p P := by
  rcases h with ⟨c, hc⟩
  exact ⟨modP p c, by rw [hc, modP_mul]⟩

/-- Coprimality against a fixed left factor lifts across a right-hand
`Array.polyProduct` of a list, provided it holds against each list member. -/
private theorem commonDvdOne_polyProduct_right (a : FpPoly p) :
    ∀ (R : List ZPoly),
      (∀ b ∈ R, CommonDvdOne a (modP p b)) →
      CommonDvdOne a (modP p (Array.polyProduct R.toArray))
  | [], _ => by
      intro e _ he1
      have hone : modP p (Array.polyProduct ([] : List ZPoly).toArray) = 1 := by simp
      rw [hone] at he1
      exact he1
  | b :: rest, h => by
      rw [ZPoly.polyProduct_cons_toArray, modP_mul]
      exact CommonDvdOne.mul (h b (by simp))
        (commonDvdOne_polyProduct_right a rest
          (fun c hc => h c (List.mem_cons_of_mem b hc)))

/-- Coprimality against a fixed right factor lifts across a left-hand
`Array.polyProduct` of a list, provided it holds against each list member. -/
private theorem commonDvdOne_polyProduct_left (X : FpPoly p) :
    ∀ (L : List ZPoly),
      (∀ a ∈ L, CommonDvdOne (modP p a) X) →
      CommonDvdOne (modP p (Array.polyProduct L.toArray)) X
  | [], _ => by
      intro e he1 _
      have hone : modP p (Array.polyProduct ([] : List ZPoly).toArray) = 1 := by simp
      rw [hone] at he1
      exact he1
  | a :: rest, h => by
      rw [ZPoly.polyProduct_cons_toArray, modP_mul]
      exact (CommonDvdOne.mul (h a (by simp)).symm
        (commonDvdOne_polyProduct_left X rest
          (fun c hc => h c (List.mem_cons_of_mem a hc))).symm).symm

/-- Cross coprimality of every left member with every right member lifts to
coprimality of the two ordered products. -/
private theorem commonDvdOne_products (L R : List ZPoly)
    (h : ∀ a ∈ L, ∀ b ∈ R, CommonDvdOne (modP p a) (modP p b)) :
    CommonDvdOne (modP p (Array.polyProduct L.toArray))
      (modP p (Array.polyProduct R.toArray)) := by
  apply commonDvdOne_polyProduct_left
  intro a ha
  exact commonDvdOne_polyProduct_right (modP p a) R (fun b hb => h a ha b hb)

omit [ZMod64.PrimeModulus p] in
/-- The linear multifactor invariant supplies target-free pairwise coprimality
of the mod-`p` factor images: at each sequential split the Bezout witness
gives `CommonDvdOne (modP g) (modP (∏ tail))`, from which coprimality of the
head against every tail member follows. -/
private theorem pairwise_commonDvdOne_of_multifactor (k : Nat)
    (factors : List ZPoly) :
    ∀ f, MultifactorLiftInvariant p k f factors →
      List.Pairwise (fun a b => CommonDvdOne (modP p a) (modP p b)) factors := by
  induction factors with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons g rest ih =>
      intro f hinv
      cases rest with
      | nil => exact List.Pairwise.cons (by simp) List.Pairwise.nil
      | cons h tail =>
          rcases hinv with ⟨hstart, _, _, htail⟩
          have hbez_fp :
              (Hex.ZPoly.normalizedXGCD p g (Array.polyProduct (h :: tail).toArray)).left *
                  modP p g +
                (Hex.ZPoly.normalizedXGCD p g (Array.polyProduct (h :: tail).toArray)).right *
                  modP p (Array.polyProduct (h :: tail).toArray) = 1 := by
            have hb := hstart.2.1
            rw [modP_reduceModPow_of_pos p 1 g (by omega),
              modP_reduceModPow_of_pos p 1 _ (by omega)] at hb
            exact fpPoly_eq_one_of_congr_liftToZ _ hb
          have hcommon_head :
              CommonDvdOne (modP p g) (modP p (Array.polyProduct (h :: tail).toArray)) :=
            commonDvdOne_of_bezout hbez_fp
          refine List.Pairwise.cons ?_ (ih _ htail)
          intro b hb e he_g he_b
          have hbdvd : modP p b ∣ modP p (Array.polyProduct (h :: tail).toArray) :=
            modP_dvd_of_dvd (zpoly_dvd_polyProduct (h :: tail) hb)
          exact hcommon_head e he_g (fp_dvd_trans he_b hbdvd)

/-- Balanced split coprimality (`ZCoprimeSplits`) follows from target-free
pairwise coprimality of the mod-`p` factor images. -/
private theorem zcoprime_of_pairwise (factors : List ZPoly) :
    List.Pairwise (fun a b => CommonDvdOne (modP p a) (modP p b)) factors →
    ZCoprimeSplits p factors := by
  induction factors using ZCoprimeSplits.induct with
  | case1 => intro _; simp only [ZCoprimeSplits]
  | case2 g => intro _; simp only [ZCoprimeSplits]
  | case3 g₀ g₁ rest gs half L R ihL ihR =>
      intro hpw
      have hsplit : L ++ R = g₀ :: g₁ :: rest := List.take_append_drop _ _
      rw [← hsplit] at hpw
      obtain ⟨hpwL, hpwR, hcross⟩ := List.pairwise_append.mp hpw
      rw [ZCoprimeSplits]
      exact ⟨normalizedXGCD_gcd_eq_one_of_common_dvd_one p _ _
        (commonDvdOne_products L R hcross), ihL hpwL, ihR hpwR⟩

end LinearToZCoprimeBridge

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
  have hp : 1 < p := (Fact.out (p := Nat.Prime p)).one_lt
  cases factors with
  | nil => exact absurd rfl hnonempty
  | cons g rest =>
      cases rest with
      | nil => simp [Hex.ZPoly.QuadraticMultifactorLiftInvariant]
      | cons h tail =>
          -- Product congruence to `f'` modulo `p`, from the linear invariant.
          have hprod_raw : Hex.ZPoly.congr
              (Array.polyProduct (g :: h :: tail).toArray) f' p := by
            rcases hinv with ⟨hstart, _, _, _⟩
            have hstart1 := hstart.1
            -- `hstart1 : congr (reduceModPow g p 1 * reduceModPow (∏ (h::tail)) p 1) f (p^1)`
            have hprod_reduced :
                Hex.ZPoly.congr
                  (Hex.ZPoly.reduceModPow g p 1 *
                    Hex.ZPoly.reduceModPow
                      (Array.polyProduct (h :: tail).toArray) p 1) f p := by
              simpa [Nat.pow_one] using hstart1
            have hreduce_prod :
                Hex.ZPoly.congr
                  (Hex.ZPoly.reduceModPow g p 1 *
                    Hex.ZPoly.reduceModPow
                      (Array.polyProduct (h :: tail).toArray) p 1)
                  (g * Array.polyProduct (h :: tail).toArray) p := by
              apply Hex.ZPoly.congr_mul
              · simpa [Nat.pow_one] using
                  Hex.ZPoly.congr_reduceModPow g p 1
                    (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
              · simpa [Nat.pow_one] using
                  Hex.ZPoly.congr_reduceModPow
                    (Array.polyProduct (h :: tail).toArray) p 1
                    (Nat.pow_pos (Hex.ZMod64.Bounds.pPos (p := p)))
            have hprod_raw_f :
                Hex.ZPoly.congr
                  (g * Array.polyProduct (h :: tail).toArray) f p :=
              Hex.ZPoly.congr_trans _ _ _ p
                (Hex.ZPoly.congr_symm _ _ _ hreduce_prod) hprod_reduced
            rw [Hex.ZPoly.polyProduct_cons_toArray]
            exact Hex.ZPoly.congr_trans _ _ _ p hprod_raw_f htarget
          exact inv_of_ZCoprimeSplits p k f' (g :: h :: tail) hp hk hmonic
            hprod_raw
            (zcoprime_of_pairwise (g :: h :: tail)
              (pairwise_commonDvdOne_of_multifactor k (g :: h :: tail) f hinv))
            (by simp)

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
      simpa [Hex.ZPoly.QuadraticMultifactorLiftInvariant,
        Hex.ZPoly.MultifactorLiftInvariant] using hinv
  | cons g rest =>
      exact
        quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant_congr
          p k f f (g :: rest) hk hmonic (Hex.ZPoly.congr_refl f p)
          (by simp) hinv

section QuadraticOutputBridge
open Hex

/-- Local length lemma for the balanced quadratic list lifter. -/
private theorem quad_toList_length (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly) :
    (ZPoly.multifactorLiftQuadraticList p k f factors).toList.length = factors.length := by
  induction f, factors using ZPoly.multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => simp [ZPoly.multifactorLiftQuadraticList]
  | case2 f _g => simp [ZPoly.multifactorLiftQuadraticList]
  | case3 f g₀ g₁ rest =>
      rename_i ihL ihR
      rw [ZPoly.multifactorLiftQuadraticList, Array.toList_append, List.length_append,
        ihL, ihR, ← List.length_append, List.take_append_drop]

/-- Per-index congruence transports across list concatenation with matching
prefix length. Local copy of the private balanced-tree bookkeeping lemma. -/
private theorem congr_getD_append (p : Nat) (o1 o2 f1 f2 : List ZPoly)
    (hlen : o1.length = f1.length)
    (h1 : ∀ (i : Nat), ZPoly.congr (o1[i]?.getD 0) (f1[i]?.getD 0) p)
    (h2 : ∀ (i : Nat), ZPoly.congr (o2[i]?.getD 0) (f2[i]?.getD 0) p) :
    ∀ (i : Nat), ZPoly.congr ((o1 ++ o2)[i]?.getD 0) ((f1 ++ f2)[i]?.getD 0) p := by
  intro i
  by_cases hi : i < o1.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hlen ▸ hi)]
    exact h1 i
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi),
        List.getElem?_append_right (hlen ▸ Nat.le_of_not_lt hi), hlen]
    exact h2 (i - f1.length)

/-- Monic-free per-output mod-`p` preservation for the balanced quadratic list
lifter: each output is congruent modulo `p` to the corresponding input factor.
This drops the raw-monicity hypothesis of the executable-side companion, which
is only used there to feed the recursion. -/
private theorem quad_each_congr_mod_base (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly) (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : ZPoly.QuadraticMultifactorLiftInvariant p k f factors)
    (hproduct : ZPoly.congr (Array.polyProduct factors.toArray) f p) :
    ∀ (i : Nat),
      ZPoly.congr
        ((ZPoly.multifactorLiftQuadraticList p k f factors).toList[i]?.getD 0)
        (factors[i]?.getD 0) p := by
  induction f, factors using ZPoly.multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => intro i; rw [ZPoly.multifactorLiftQuadraticList]; simp; exact ZPoly.congr_refl 0 p
  | case2 f _g =>
      intro i
      rw [ZPoly.multifactorLiftQuadraticList]
      match i with
      | 0 =>
          simp only [List.getElem?_cons_zero, Option.getD_some]
          have hg : ZPoly.congr _g f p := by
            simpa [Array.polyProduct] using hproduct
          have hred : ZPoly.congr (ZPoly.reduceModPow f p k) f p := by
            have h1 : ZPoly.congr (ZPoly.reduceModPow f p k) f (p ^ k) :=
              ZPoly.congr_reduceModPow f p k (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
            have h2 := ZPoly.congr_pow_of_le p 1 k _ _ hk h1
            simpa [Nat.pow_one] using h2
          exact ZPoly.congr_trans _ _ _ p hred (ZPoly.congr_symm _ _ _ hg)
      | Nat.succ i' => simp; exact ZPoly.congr_refl 0 p
  | case3 f g₀ g₁ rest gs half L R gg hh xg ss tt lifted ihL ihR =>
      simp only [ZPoly.QuadraticMultifactorLiftInvariant] at hinv
      obtain ⟨hstart, hinvL, hinvR⟩ := hinv
      have hgc := ZPoly.henselLiftQuadratic_g_congr_mod_base p k f _ _ _ _ hk hp hstart
      have hhc := ZPoly.henselLiftQuadratic_h_congr_mod_base p k f _ _ _ _ hk hp hstart
      have ihL' := ihL hinvL (ZPoly.congr_symm _ _ _ hgc)
      have ihR' := ihR hinvR (ZPoly.congr_symm _ _ _ hhc)
      have hlen := quad_toList_length p k lifted.g L
      have key := congr_getD_append p _ _ L R hlen ihL' ihR'
      rw [List.take_append_drop] at key
      intro i
      rw [ZPoly.multifactorLiftQuadraticList, Array.toList_append]
      exact key i

/-- Target-monic per-output monicity for the balanced quadratic list lifter
(list-membership form). Local copy of the private executable-side companion. -/
private theorem quad_list_each_monic (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly) (hk : 1 ≤ k) (hp : 1 < p)
    (hf_monic : DensePoly.Monic f)
    (hinv : ZPoly.QuadraticMultifactorLiftInvariant p k f factors) :
    ∀ entry ∈ (ZPoly.multifactorLiftQuadraticList p k f factors).toList,
      DensePoly.Monic entry := by
  induction f, factors using ZPoly.multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => rw [ZPoly.multifactorLiftQuadraticList]; intro entry hmem; simp at hmem
  | case2 f _g =>
      rw [ZPoly.multifactorLiftQuadraticList]
      intro entry hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ZPoly.reduceModPow_monic_of_monic p k' f hp hf_monic
  | case3 f g₀ g₁ rest =>
      rename_i ihL ihR
      simp only [ZPoly.QuadraticMultifactorLiftInvariant] at hinv
      obtain ⟨hstart, hinvL, hinvR⟩ := hinv
      have ihL' := ihL (ZPoly.henselLiftQuadratic_g_monic p k f _ _ _ _ hk hp hstart) hinvL
      have ihR' := ihR (ZPoly.henselLiftQuadratic_h_monic p k f _ _ _ _ hk hp hf_monic hstart) hinvR
      rw [ZPoly.multifactorLiftQuadraticList]
      intro entry hmem
      rw [Array.toList_append, List.mem_append] at hmem
      rcases hmem with h | h
      · exact ihL' entry h
      · exact ihR' entry h

/-- Every balanced quadratic output *except the last* is monic, with no
monic-target hypothesis. Each split's left factor `lifted.g` is monic by
`henselLiftQuadratic_g_monic` alone, so the whole left subtree is monic; only
the global-rightmost leaf (a right-spine `reduceModPow` of the cofactor) needs a
monic target, and it is excluded here. -/
private theorem quad_all_but_last_monic (p k : Nat) [ZMod64.Bounds p]
    (f : ZPoly) (factors : List ZPoly) (hk : 1 ≤ k) (hp : 1 < p)
    (hinv : ZPoly.QuadraticMultifactorLiftInvariant p k f factors) :
    ∀ (i : Nat), i + 1 < (ZPoly.multifactorLiftQuadraticList p k f factors).toList.length →
      DensePoly.Monic ((ZPoly.multifactorLiftQuadraticList p k f factors).toList[i]?.getD 0) := by
  induction f, factors using ZPoly.multifactorLiftQuadraticList.induct (p := p) (k := k) with
  | case1 f => intro i hi; rw [ZPoly.multifactorLiftQuadraticList] at hi; simp at hi
  | case2 f _g => intro i hi; rw [ZPoly.multifactorLiftQuadraticList] at hi; simp at hi
  | case3 f g₀ g₁ rest gs half L R gg hh xg ss tt lifted ihL ihR =>
      simp only [ZPoly.QuadraticMultifactorLiftInvariant] at hinv
      obtain ⟨hstart, hinvL, hinvR⟩ := hinv
      have hg_monic := ZPoly.henselLiftQuadratic_g_monic p k f _ _ _ _ hk hp hstart
      have hLmonic := quad_list_each_monic p k lifted.g L hk hp hg_monic hinvL
      have ihR' := ihR hinvR
      have hlenL := quad_toList_length p k lifted.g L
      intro i hi
      rw [ZPoly.multifactorLiftQuadraticList, Array.toList_append] at hi ⊢
      set oL := (ZPoly.multifactorLiftQuadraticList p k lifted.g L).toList with hoL
      set oR := (ZPoly.multifactorLiftQuadraticList p k lifted.h R).toList with hoR
      rw [List.length_append] at hi
      by_cases hiL : i < oL.length
      · rw [List.getElem?_append_left hiL, List.getElem?_eq_getElem hiL, Option.getD_some]
        exact hLmonic _ (List.getElem_mem hiL)
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hiL)]
        exact ihR' (i - oL.length) (by omega)

/-- Congruence of ordered products from pointwise (getD-form) congruence of two
equal-length lists. -/
private theorem congr_polyProduct_of_pointwise (p : Nat) [ZMod64.Bounds p] :
    ∀ (l1 l2 : List ZPoly), l1.length = l2.length →
      (∀ (i : Nat), ZPoly.congr (l1[i]?.getD 0) (l2[i]?.getD 0) p) →
      ZPoly.congr (Array.polyProduct l1.toArray) (Array.polyProduct l2.toArray) p
  | [], [], _, _ => ZPoly.congr_refl _ p
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | a :: as, b :: bs, hlen, h => by
      rw [ZPoly.polyProduct_cons_toArray, ZPoly.polyProduct_cons_toArray]
      apply ZPoly.congr_mul
      · exact h 0
      · exact congr_polyProduct_of_pointwise p as bs
          (by simpa using hlen) (fun i => h (i + 1))

/-- The abstract lock-step engine behind the linear/quadratic agreement. It
inducts on the factor list following the *linear* (sequential) recursion, and
compares against an abstract output list `out` constrained only by its length,
its per-output mod-`p` residues, all-but-last monicity, and its product modulo
`p ^ k`. At each non-singleton peel `hensel_unique` identifies the linear head
with `out.head` and the linear complement with the product of `out.tail`; the
complement equality is exactly the recursive target congruence. -/
private theorem output_map_eq_linear (p k : Nat) [Fact (Nat.Prime p)]
    [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (f : ZPoly) (factors out : List ZPoly)
    (hk : 1 ≤ k) (hp : 1 < p)
    (hlen : out.length = factors.length)
    (hout_monic : ∀ (i : Nat), i + 1 < out.length → DensePoly.Monic (out[i]?.getD 0))
    (hout_base : ∀ (i : Nat), ZPoly.congr (out[i]?.getD 0) (factors[i]?.getD 0) p)
    (hout_prod : ZPoly.congr (Array.polyProduct out.toArray) f (p ^ k))
    (hinv : ZPoly.MultifactorLiftInvariant p k f factors) :
    (ZPoly.multifactorLiftList p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map (Int.castRingHom (ZMod (p ^ k)))) =
      out.map
        (fun g => (HexPolyMathlib.toPolynomial g).map (Int.castRingHom (ZMod (p ^ k)))) := by
  induction factors generalizing f out with
  | nil =>
      have hout_nil : out = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hout_nil
      simp [ZPoly.multifactorLiftList]
  | cons g rest ih =>
      cases rest with
      | nil =>
          -- `factors = [g]`, so `out = [G]`.
          match out, hlen, hout_prod with
          | [G], _, hout_prod =>
              have hGf : ZPoly.congr G f (p ^ k) := by
                simpa [Array.polyProduct] using hout_prod
              have hcongr : ZPoly.congr (ZPoly.reduceModPow f p k) G (p ^ k) :=
                ZPoly.congr_trans _ _ _ (p ^ k)
                  (ZPoly.congr_reduceModPow f p k
                    (Nat.pow_pos (ZMod64.Bounds.pPos (p := p))))
                  (ZPoly.congr_symm _ _ _ hGf)
              have hmap := zpoly_congr_toPolynomial_map_eq
                (ZPoly.reduceModPow f p k) G (p ^ k) hcongr
              simpa [ZPoly.multifactorLiftList] using hmap
      | cons h tail =>
          match out, hlen, hout_monic, hout_base, hout_prod with
          | G :: r, hlen, hout_monic, hout_base, hout_prod =>
              rcases hinv with ⟨hstart, hstepDeg, hstepBez, htail⟩
              set splitProduct : ZPoly := Array.polyProduct (h :: tail).toArray with hsplit
              set xgcd := ZPoly.normalizedXGCD p g splitProduct with hxgcd
              set s : ZPoly := Hex.FpPoly.liftToZ xgcd.left with hs
              set t : ZPoly := Hex.FpPoly.liftToZ xgcd.right with ht
              set linearLifted := ZPoly.henselLift p k f g splitProduct xgcd.left xgcd.right
                with hll
              have hstart' :
                  ZPoly.LinearLiftLoopInvariant p 1 f xgcd.left xgcd.right
                    { g := ZPoly.reduceModPow g p 1
                      h := ZPoly.reduceModPow splitProduct p 1 } := hstart
              have hlin_prod :
                  ZPoly.congr (linearLifted.g * linearLifted.h) f (p ^ k) :=
                ZPoly.henselLift_spec p k f g splitProduct xgcd.left xgcd.right hk hp
                  hstart' hstepDeg hstepBez
              have hlin_g_monic : DensePoly.Monic linearLifted.g :=
                ZPoly.henselLift_monic p k f g splitProduct xgcd.left xgcd.right hk hp
                  hstart' hstepDeg hstepBez
              -- Bezout congruence for the mod-`p` coprimality of the linear split.
              have hbez_reduced :
                  ZPoly.congr
                    (Hex.FpPoly.liftToZ
                      (xgcd.left * ZPoly.modP p g + xgcd.right * ZPoly.modP p splitProduct)) 1 p := by
                simpa [ZPoly.modP_reduceModPow_of_pos p 1 g (by omega),
                  ZPoly.modP_reduceModPow_of_pos p 1 splitProduct (by omega)]
                  using hstart'.2.1
              have hbez_lift :
                  ZPoly.congr
                    (Hex.FpPoly.liftToZ
                      (xgcd.left * ZPoly.modP p g + xgcd.right * ZPoly.modP p splitProduct))
                    (s * g + t * splitProduct) p := by
                apply ZPoly.congr_liftToZ_of_modP_eq
                simp [hs, ht]
              have hbez : ZPoly.congr (s * g + t * splitProduct) 1 p :=
                ZPoly.congr_trans _ _ _ p
                  (ZPoly.congr_symm _ _ _ hbez_lift) hbez_reduced
              -- Base-prime facts.
              have hlin_g_base : ZPoly.congr linearLifted.g g p :=
                ZPoly.henselLift_g_congr_mod_base p k f g splitProduct
                  xgcd.left xgcd.right hk
              have hlin_h_base : ZPoly.congr linearLifted.h splitProduct p :=
                ZPoly.henselLift_h_congr_mod_base p k f g splitProduct
                  xgcd.left xgcd.right hk
              -- `out`-side facts.
              have hlen' : r.length = (h :: tail).length := by
                simpa using hlen
              have hrpos : 0 < r.length := by rw [hlen']; simp
              have hGmonic : DensePoly.Monic G := by
                have := hout_monic 0 (by simp only [List.length_cons]; omega)
                simpa using this
              have hGbase : ZPoly.congr G g p := by
                have := hout_base 0
                simpa using this
              have hr_base : ∀ (i : Nat),
                  ZPoly.congr (r[i]?.getD 0) ((h :: tail)[i]?.getD 0) p := by
                intro i
                have := hout_base (i + 1)
                simpa using this
              have hr_monic : ∀ (i : Nat), i + 1 < r.length →
                  DensePoly.Monic (r[i]?.getD 0) := by
                intro i hi
                have := hout_monic (i + 1) (by simpa using hi)
                simpa using this
              have hprodGr : ZPoly.congr (G * Array.polyProduct r.toArray) f (p ^ k) := by
                have := hout_prod
                rwa [ZPoly.polyProduct_cons_toArray] at this
              -- Mathlib-side inputs to `hensel_unique`.
              have hg : (HexPolyMathlib.toPolynomial linearLifted.g).Monic :=
                toPolynomial_monic_of_dense_monic _ hlin_g_monic
              have hg' : (HexPolyMathlib.toPolynomial G).Monic :=
                toPolynomial_monic_of_dense_monic _ hGmonic
              have hg1 :
                  (HexPolyMathlib.toPolynomial linearLifted.g).map (Int.castRingHom (ZMod p)) =
                    (HexPolyMathlib.toPolynomial G).map (Int.castRingHom (ZMod p)) :=
                zpoly_congr_toPolynomial_map_eq _ _ p
                  (ZPoly.congr_trans _ _ _ p hlin_g_base (ZPoly.congr_symm _ _ _ hGbase))
              have hh1 :
                  (HexPolyMathlib.toPolynomial linearLifted.h).map (Int.castRingHom (ZMod p)) =
                    (HexPolyMathlib.toPolynomial (Array.polyProduct r.toArray)).map
                      (Int.castRingHom (ZMod p)) := by
                have hpr : ZPoly.congr (Array.polyProduct r.toArray) splitProduct p := by
                  have := congr_polyProduct_of_pointwise p r (h :: tail) hlen' hr_base
                  simpa [hsplit] using this
                exact zpoly_congr_toPolynomial_map_eq _ _ p
                  (ZPoly.congr_trans _ _ _ p hlin_h_base (ZPoly.congr_symm _ _ _ hpr))
              have hdeg :
                  (HexPolyMathlib.toPolynomial linearLifted.g).natDegree =
                    (HexPolyMathlib.toPolynomial G).natDegree :=
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
                  (HexPolyMathlib.toPolynomial G).map (Int.castRingHom (ZMod (p ^ k))) *
                      (HexPolyMathlib.toPolynomial (Array.polyProduct r.toArray)).map
                        (Int.castRingHom (ZMod (p ^ k))) =
                    (HexPolyMathlib.toPolynomial f).map (Int.castRingHom (ZMod (p ^ k))) := by
                have hmap := zpoly_congr_toPolynomial_map_eq
                  (G * Array.polyProduct r.toArray) f (p ^ k) hprodGr
                simpa [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul] using hmap
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
                (HexPolyMathlib.toPolynomial G)
                (HexPolyMathlib.toPolynomial (Array.polyProduct r.toArray))
                p k (by omega) hg hg' hdeg hprod hprod' hg1 hh1 hcop
              -- Recurse on the lifted complement with target `linearLifted.h`, output `r`.
              have hr_prod : ZPoly.congr (Array.polyProduct r.toArray) linearLifted.h (p ^ k) :=
                ZPoly.congr_symm _ _ _
                  (zpoly_congr_of_toPolynomial_map_eq linearLifted.h
                    (Array.polyProduct r.toArray) (p ^ k) hheq)
              have hrec := ih linearLifted.h r hlen' hr_monic hr_base hr_prod htail
              have hexpandL :
                  (ZPoly.multifactorLiftList p k f (g :: h :: tail)).toList =
                    linearLifted.g ::
                      (ZPoly.multifactorLiftList p k linearLifted.h (h :: tail)).toList := by
                simp [ZPoly.multifactorLiftList, hsplit, hxgcd, hll]
              rw [hexpandL, List.map_cons, List.map_cons]
              exact List.cons_eq_cons.mpr ⟨hgeq, hrec⟩

/-- The ordered product of a non-singleton factor list is congruent modulo `p`
to any target `f'` congruent to the linear target `f`, extracted from the
sequential linear invariant's mod-`p` loop start. -/
private theorem congr_polyProduct_target (p k : Nat) [ZMod64.Bounds p]
    (f f' g h : ZPoly) (tail : List ZPoly)
    (htarget : ZPoly.congr f f' p)
    (hinv : ZPoly.MultifactorLiftInvariant p k f (g :: h :: tail)) :
    ZPoly.congr (Array.polyProduct (g :: h :: tail).toArray) f' p := by
  rcases hinv with ⟨hstart, _, _, _⟩
  have hprod_reduced :
      ZPoly.congr
        (ZPoly.reduceModPow g p 1 *
          ZPoly.reduceModPow (Array.polyProduct (h :: tail).toArray) p 1) f p := by
    simpa [Nat.pow_one] using hstart.1
  have hreduce_prod :
      ZPoly.congr
        (ZPoly.reduceModPow g p 1 *
          ZPoly.reduceModPow (Array.polyProduct (h :: tail).toArray) p 1)
        (g * Array.polyProduct (h :: tail).toArray) p := by
    apply ZPoly.congr_mul
    · simpa [Nat.pow_one] using
        ZPoly.congr_reduceModPow g p 1 (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
    · simpa [Nat.pow_one] using
        ZPoly.congr_reduceModPow (Array.polyProduct (h :: tail).toArray) p 1
          (Nat.pow_pos (ZMod64.Bounds.pPos (p := p)))
  have hprod_raw_f : ZPoly.congr (g * Array.polyProduct (h :: tail).toArray) f p :=
    ZPoly.congr_trans _ _ _ p (ZPoly.congr_symm _ _ _ hreduce_prod) hprod_reduced
  rw [ZPoly.polyProduct_cons_toArray]
  exact ZPoly.congr_trans _ _ _ p hprod_raw_f htarget

end QuadraticOutputBridge

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
  have htarget_p : Hex.ZPoly.congr f f' p := by
    have h := Hex.ZPoly.congr_pow_of_le p 1 k f f' hk htarget
    simpa [Nat.pow_one] using h
  cases factors with
  | nil =>
      simp [Hex.ZPoly.multifactorLiftList, Hex.ZPoly.multifactorLiftQuadraticList]
  | cons g rest =>
      cases rest with
      | nil =>
          have hred : Hex.ZPoly.reduceModPow f p k = Hex.ZPoly.reduceModPow f' p k :=
            Hex.ZPoly.reduceModPow_eq_of_congr f f' p k htarget
          simp [Hex.ZPoly.multifactorLiftList, Hex.ZPoly.multifactorLiftQuadraticList, hred]
      | cons h tail =>
          have hne : (g :: h :: tail) ≠ [] := by simp
          have hqinv :
              Hex.ZPoly.QuadraticMultifactorLiftInvariant p k f' (g :: h :: tail) :=
            quadraticMultifactorLiftInvariant_of_multifactorLiftInvariant_congr
              p k f f' (g :: h :: tail) hk hmonic htarget_p hne hinv
          have hprod_p :
              Hex.ZPoly.congr (Array.polyProduct (g :: h :: tail).toArray) f' p :=
            congr_polyProduct_target p k f f' g h tail htarget_p hinv
          set out := Hex.ZPoly.multifactorLiftQuadraticList p k f' (g :: h :: tail) with hout
          have hlen : out.toList.length = (g :: h :: tail).length :=
            quad_toList_length p k f' (g :: h :: tail)
          have hout_base : ∀ (i : Nat),
              Hex.ZPoly.congr (out.toList[i]?.getD 0) ((g :: h :: tail)[i]?.getD 0) p :=
            quad_each_congr_mod_base p k f' (g :: h :: tail) hk hp hqinv hprod_p
          have hout_monic : ∀ (i : Nat), i + 1 < out.toList.length →
              Hex.DensePoly.Monic (out.toList[i]?.getD 0) :=
            quad_all_but_last_monic p k f' (g :: h :: tail) hk hp hqinv
          have hqprod :
              Hex.ZPoly.congr (Array.polyProduct out) f' (p ^ k) := by
            have h := Hex.ZPoly.multifactorLiftQuadratic_spec p k f' (g :: h :: tail).toArray hk hp
              (by simpa [Hex.ZPoly.multifactorLiftQuadratic] using hqinv)
            simpa [Hex.ZPoly.multifactorLiftQuadratic, hout] using h
          have hout_prod :
              Hex.ZPoly.congr (Array.polyProduct out.toList.toArray) f (p ^ k) := by
            have htoarr : out.toList.toArray = out := by simp
            rw [htoarr]
            exact Hex.ZPoly.congr_trans _ _ _ (p ^ k) hqprod
              (Hex.ZPoly.congr_symm _ _ _ htarget)
          exact output_map_eq_linear p k f (g :: h :: tail) out.toList hk hp hlen
            hout_monic hout_base hout_prod hinv

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
