/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexHensel
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Tactic.LinearCombination

public section

/-!
Initial coprimality-lifting infrastructure for `HexHenselMathlib`.

This module sets up the `Polynomial ℤ` statements that later Hensel-correctness
and uniqueness proofs need: coefficientwise divisibility transport through
`Polynomial.map`, compatibility of the reduction maps
`ZMod (p^(k+1)) → ZMod (p^k) → ZMod p`, the nilpotent-unit lemma for
`1 + p * u`, and the coprimality-lifting theorem surface itself.
-/

namespace HexHenselMathlib

open Polynomial

noncomputable section

/-- Reducing an integer coefficient modulo `p` gives zero exactly when `p` divides it. -/
theorem coeff_map_intCastRingHom_eq_zero_iff_dvd
    (f : Polynomial ℤ) (p n : ℕ) :
    (f.map (Int.castRingHom (ZMod p))).coeff n = 0 ↔ (p : ℤ) ∣ f.coeff n := by
  simp [Polynomial.coeff_map, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Equality after coefficientwise reduction modulo `p` is equivalent to divisibility of the coefficient difference. -/
theorem coeff_map_intCastRingHom_eq_iff_dvd_sub
    (f g : Polynomial ℤ) (p n : ℕ) :
    (f.map (Int.castRingHom (ZMod p))).coeff n =
        (g.map (Int.castRingHom (ZMod p))).coeff n ↔
      (p : ℤ) ∣ f.coeff n - g.coeff n := by
  rw [← sub_eq_zero, ← coeff_sub, ← Polynomial.map_sub]
  simpa using coeff_map_intCastRingHom_eq_zero_iff_dvd (f := f - g) p n

/-- Exact divisibility lets us recover an integer coefficient from its quotient. -/
theorem coeff_ediv_mul_eq_of_dvd {f : Polynomial ℤ} {m n : ℕ}
    (h : (m : ℤ) ∣ f.coeff n) :
    (f.coeff n / m) * m = f.coeff n := by
  exact Int.ediv_mul_cancel h

/-- Exact divisibility also gives the left-multiplication form used in coefficientwise quotient rewrites. -/
theorem coeff_mul_ediv_eq_of_dvd {f : Polynomial ℤ} {m n : ℕ}
    (h : (m : ℤ) ∣ f.coeff n) :
    (m : ℤ) * (f.coeff n / m) = f.coeff n := by
  rw [Int.mul_comm, Int.ediv_mul_cancel h]

/-- Reducing coefficients from `ZMod (p^(k+1))` to `ZMod p` agrees with direct reduction. -/
theorem zmod_castHom_comp_intCastRingHom_pow_succ
    (p k : ℕ) :
    (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)).comp
        (Int.castRingHom (ZMod (p ^ (k + 1)))) =
      Int.castRingHom (ZMod p) := by
  ext z
  simp

/-- Reducing coefficients from `ZMod (p^(k+1))` to `ZMod (p^k)` agrees with direct reduction. -/
theorem zmod_castHom_comp_intCastRingHom_pow_step
    (p k : ℕ) :
    (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))).comp
        (Int.castRingHom (ZMod (p ^ (k + 1)))) =
      Int.castRingHom (ZMod (p ^ k)) := by
  ext z
  simp

/-- Polynomial reduction from `ZMod (p^(k+1))` to `ZMod p` is compatible with direct reduction. -/
theorem polynomial_map_zmod_pow_succ_to_base
    (f : Polynomial ℤ) (p k : ℕ) :
    (f.map (Int.castRingHom (ZMod (p ^ (k + 1))))).map
        (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)) =
      f.map (Int.castRingHom (ZMod p)) := by
  rw [map_map]
  simp [zmod_castHom_comp_intCastRingHom_pow_succ]

/-- Polynomial reduction from `ZMod (p^(k+1))` to `ZMod (p^k)` is compatible with direct reduction. -/
theorem polynomial_map_zmod_pow_succ_to_pow
    (f : Polynomial ℤ) (p k : ℕ) :
    (f.map (Int.castRingHom (ZMod (p ^ (k + 1))))).map
        (ZMod.castHom (Nat.pow_dvd_pow p (Nat.le_succ k)) (ZMod (p ^ k))) =
      f.map (Int.castRingHom (ZMod (p ^ k))) := by
  rw [map_map]
  simp [zmod_castHom_comp_intCastRingHom_pow_step]

/-- In `Polynomial (ZMod (p^k))`, the correction term `p * u` is nilpotent, so `1 + p * u` is a unit. -/
theorem isUnit_one_add_C_mul
    (p k : ℕ) (u : Polynomial (ZMod (p ^ k))) :
    IsUnit (1 + Polynomial.C (p : ZMod (p ^ k)) * u) := by
  have hnil : IsNilpotent (Polynomial.C (p : ZMod (p ^ k)) * u) := by
    refine ⟨k, ?_⟩
    rw [mul_pow, ← Polynomial.C_pow]
    have hp_pow : (p : ZMod (p ^ k)) ^ k = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    rw [hp_pow, Polynomial.C_0, zero_mul]
  exact hnil.isUnit_one_add

/-- Coprimality modulo `p` lifts to coprimality modulo `p^k`.

The `0 < k` hypothesis is part of the calling convention; the proof does not
need it (the `k = 0` case is vacuous because `ZMod 1` is the zero ring). -/
theorem coprime_mod_p_lifts (g h : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (_hk : 0 < k) :
    IsCoprime (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p))) →
    IsCoprime (g.map (Int.castRingHom (ZMod (p ^ k))))
              (h.map (Int.castRingHom (ZMod (p ^ k)))) := by
  rintro ⟨a₀, b₀, hab⟩
  obtain ⟨A, hA⟩ :=
    Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective a₀
  obtain ⟨B, hB⟩ :=
    Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective b₀
  have hcombo_modp : (A * g + B * h).map (Int.castRingHom (ZMod p)) = 1 := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, hA, hB, hab]
  have hsub_modp : (A * g + B * h - 1).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_one, hcombo_modp, sub_self]
  have hdvd : ∀ n, (p : ℤ) ∣ (A * g + B * h - 1).coeff n := by
    intro n
    rw [← coeff_map_intCastRingHom_eq_zero_iff_dvd]
    have h := congr_arg (fun q : Polynomial (ZMod p) => q.coeff n) hsub_modp
    simpa using h
  obtain ⟨U, hU⟩ :=
    (Polynomial.C_dvd_iff_dvd_coeff (p : ℤ) (A * g + B * h - 1)).mpr hdvd
  set Φpk : ℤ →+* ZMod (p ^ k) := Int.castRingHom (ZMod (p ^ k)) with hΦpk_def
  have hp_cast : Φpk (p : ℤ) = (p : ZMod (p ^ k)) := by
    simp [hΦpk_def]
  have hsub_pk : (A * g + B * h - 1).map Φpk =
      Polynomial.C (p : ZMod (p ^ k)) * U.map Φpk := by
    rw [hU, Polynomial.map_mul, Polynomial.map_C, hp_cast]
  have hcombo_pk : A.map Φpk * g.map Φpk + B.map Φpk * h.map Φpk
      = 1 + Polynomial.C (p : ZMod (p ^ k)) * U.map Φpk := by
    have h := hsub_pk
    rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_one] at h
    exact sub_eq_iff_eq_add'.mp h
  have hunit : IsUnit (1 + Polynomial.C (p : ZMod (p ^ k)) * U.map Φpk) :=
    isUnit_one_add_C_mul p k _
  obtain ⟨wu, hwu⟩ := hunit
  refine ⟨(↑wu⁻¹ : Polynomial (ZMod (p ^ k))) * A.map Φpk,
          (↑wu⁻¹ : Polynomial (ZMod (p ^ k))) * B.map Φpk, ?_⟩
  have hregroup :
      ((↑wu⁻¹ : Polynomial (ZMod (p ^ k))) * A.map Φpk) * g.map Φpk +
        ((↑wu⁻¹ : Polynomial (ZMod (p ^ k))) * B.map Φpk) * h.map Φpk
      = (↑wu⁻¹ : Polynomial (ZMod (p ^ k))) *
        (A.map Φpk * g.map Φpk + B.map Φpk * h.map Φpk) := by ring
  rw [hregroup, hcombo_pk, ← hwu]
  exact Units.inv_mul wu

/--
Coprime monic cancellation with a strict degree bound.

If `a * h + b * g = 0` in `R[X]` for a commutative domain `R`, where
`g` is monic and `IsCoprime g h`, then `a.natDegree < g.natDegree`
forces both `a = 0` and `b = 0`.

This is the load-bearing analytic step for the binary-Hensel uniqueness
theorem `hensel_unique` (`HexHenselMathlib/Correctness.lean`): after
reducing the integer-polynomial difference equation modulo `p`, the
problem becomes a coprime cancellation in `Polynomial (ZMod p)`, with
the strict degree bound following from the monicity of both `g` and `g'`
at the same `natDegree`.
-/
theorem isCoprime_cancel_of_natDegree_lt
    {R : Type*} [CommRing R] [IsDomain R]
    {g h a b : Polynomial R} (hg : g.Monic) (hcop : IsCoprime g h)
    (heq : a * h + b * g = 0)
    (hdeg : a.natDegree < g.natDegree) :
    a = 0 ∧ b = 0 := by
  have hdvd_ah : g ∣ a * h := ⟨-b, by linear_combination heq⟩
  have hdvd_a : g ∣ a := hcop.dvd_of_dvd_mul_right hdvd_ah
  have ha : a = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd_a hdeg
  refine ⟨ha, ?_⟩
  rw [ha, zero_mul, zero_add] at heq
  have hg_ne : g ≠ 0 := hg.ne_zero
  exact (mul_eq_zero.mp heq).resolve_right hg_ne

end

end HexHenselMathlib
