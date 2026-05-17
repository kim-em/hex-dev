import HexHenselMathlib.Basic
import HexPolyMathlib.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Field.ZMod

/-!
Mathlib-facing correctness and uniqueness theorem surface for executable
Hensel lifting.

The statements in this module transfer the `Hex.ZPoly` Hensel API through
`HexPolyMathlib.toPolynomial`, while keeping all new content proof-only.
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

/-- The iterative executable lift gives a factorization of `f` over Mathlib polynomials modulo `p^k`. -/
theorem hensel_correct
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod (p ^ k))
    (HexPolyMathlib.toPolynomial r.g).map φ *
        (HexPolyMathlib.toPolynomial r.h).map φ =
      (HexPolyMathlib.toPolynomial f).map φ := by
  sorry

/-- The iterative executable lift extends the input factorization modulo `p`. -/
theorem hensel_extends
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    let φ := Int.castRingHom (ZMod p)
    (HexPolyMathlib.toPolynomial r.g).map φ =
        (HexPolyMathlib.toPolynomial g).map φ ∧
      (HexPolyMathlib.toPolynomial r.h).map φ =
        (HexPolyMathlib.toPolynomial h).map φ := by
  sorry

/-- The iterative executable lift preserves the Mathlib degree of the monic lifted factor. -/
theorem hensel_degree
    (f g h : Hex.ZPoly) (p k : Nat) [Hex.ZMod64.Bounds p]
    (s t : Hex.FpPoly p)
    (hk : 1 ≤ k)
    (hprod : Hex.ZPoly.congr (g * h) f p)
    (hbez :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (s * Hex.ZPoly.modP p g + t * Hex.ZPoly.modP p h))
        1 p)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.henselLift p k f g h s t
    (HexPolyMathlib.toPolynomial r.g).natDegree =
      (HexPolyMathlib.toPolynomial g).natDegree := by
  sorry

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

/-- The quadratic step preserves monicity on the lifted `g` factor in Mathlib form. -/
theorem quadraticHenselStep_monic
    (m : Nat) (f g h s t : Hex.ZPoly)
    (hm : 0 < m)
    (hmonic : Hex.DensePoly.Monic g) :
    let r := Hex.ZPoly.quadraticHenselStep m f g h s t
    (HexPolyMathlib.toPolynomial r.g).Monic := by
  sorry

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
  sorry

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
    (hinv : Hex.ZPoly.MultifactorLiftInvariant p k f factors.toList) :
    let φ := Int.castRingHom (ZMod (p ^ k))
    (Hex.ZPoly.multifactorLift p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map φ) =
      (Hex.ZPoly.multifactorLiftQuadratic p k f factors).toList.map
        (fun g => (HexPolyMathlib.toPolynomial g).map φ) := by
  sorry

end

end HexHenselMathlib
