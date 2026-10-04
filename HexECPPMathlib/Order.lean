/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Hasse
public import HexECPP.Replay
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Point orders exclude small prime divisors

If a nonidentity point in a finite group satisfies `q • Q = 0` for a prime
`q`, its order is exactly `q`. Lagrange's theorem then makes `q` a divisor
of the group size. For an elliptic curve reduced modulo a prime divisor
`p` of the candidate `n`, this gives `q ≤ #E(𝔽_p)`.

Hasse's bound and the certificate's strict size condition together rule out
`p² ≤ n`. This is the contradiction needed to prove `n` prime.
-/

@[expose] public section

namespace Hex.ECPP

set_option linter.style.haveILetI false in
/-- A nonzero point annihilated by a prime has that order, which divides the
cardinality of its finite group. -/
theorem prime_order_dvd_card {G : Type*} [AddGroup G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {Q : G} (hne : Q ≠ 0) (hzero : q • Q = 0) :
    q ∣ Fintype.card G := by
  letI : Fact q.Prime := ⟨hq⟩
  have hord : addOrderOf Q = q := addOrderOf_eq_prime hzero hne
  rw [← hord]
  exact addOrderOf_dvd_card

/-- A prime annihilating a nonzero point is at most the finite group order. -/
theorem prime_order_le_card {G : Type*} [AddGroup G] [Fintype G]
    {q : ℕ} (hq : q.Prime) {Q : G} (hne : Q ≠ 0) (hzero : q • Q = 0) :
    q ≤ Fintype.card G := by
  exact Nat.le_of_dvd Fintype.card_pos (prime_order_dvd_card hq hne hzero)

/-- The strict ECPP size check rules out a prime divisor at most `√n` once
its reduced curve has a point of order `q`. -/
theorem size_excludes_small_divisor (p n q N : ℕ) (hq2 : 2 ≤ q)
    (hsmall : p * p ≤ n) (horder : q ≤ N)
    (hhasse : ((p : ℤ) + 1 - (N : ℤ)) ^ 2 ≤ 4 * (p : ℤ))
    (hsize : sizeBound n q = true) : False := by
  let r := q - 1
  let c := r * r - n
  have hq : q = r + 1 := by dsimp [r]; omega
  have hnr : n < r * r := sizeBound_first hsize
  have hcpos : 0 < c := Nat.sub_pos_iff_lt.mpr hnr
  have hcsq : 16 * n * q < c * c := sizeBound_second hsize
  have hrp : p < r := by
    by_contra hh
    have hrle : r ≤ p := Nat.le_of_not_gt hh
    have hr2 : (r : ℤ) ^ 2 ≤ (p : ℤ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by exact_mod_cast hrle)
    have hnri : (n : ℤ) < (r : ℤ) ^ 2 := by
      have ht : (n : ℤ) < (r : ℤ) * r := by exact_mod_cast hnr
      simpa only [pow_two] using ht
    have hsmalli : (p : ℤ) ^ 2 ≤ n := by
      have ht : (p : ℤ) * p ≤ n := by exact_mod_cast hsmall
      simpa only [pow_two] using ht
    omega
  have hci : (c : ℤ) = (r : ℤ) ^ 2 - n := by
    dsimp [c]
    rw [Nat.cast_sub hnr.le]
    norm_num [pow_two]
  have hri : (r : ℤ) = q - 1 := by
    have hqi : (q : ℤ) = (r : ℤ) + 1 := by exact_mod_cast hq
    omega
  have hdnonneg : 0 ≤ (r : ℤ) - p := by
    have ht : (p : ℤ) ≤ r := by exact_mod_cast hrp.le
    omega
  have hN : (r : ℤ) + 1 ≤ N := by exact_mod_cast (hq ▸ horder)
  have hdle : ((r : ℤ) - p) ^ 2 ≤ 4 * p := by
    have hleft : (r : ℤ) - p ≤ (N : ℤ) - p - 1 := by omega
    have hright : 0 ≤ (N : ℤ) - p - 1 := by omega
    have hsq := (sq_le_sq₀ hdnonneg hright).mpr hleft
    nlinarith only [hsq, hhasse]
  have hcle : (c : ℤ) ≤ ((r : ℤ) - p) * ((r : ℤ) + p) := by
    have hsmalli : (p : ℤ) ^ 2 ≤ n := by
      have ht : (p : ℤ) * p ≤ n := by exact_mod_cast hsmall
      simpa only [pow_two] using ht
    nlinarith only [hci, hsmalli]
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hsum0 : (0 : ℤ) ≤ (r : ℤ) + p := by positivity
  have hbound1 : (c : ℤ) ^ 2 ≤ ((r : ℤ) - p) ^ 2 * ((r : ℤ) + p) ^ 2 := by
    have hsq := (sq_le_sq₀ hc0 (mul_nonneg hdnonneg hsum0)).mpr hcle
    nlinarith only [hsq]
  have hbound2 : ((r : ℤ) - p) ^ 2 * ((r : ℤ) + p) ^ 2 ≤
      4 * p * ((r : ℤ) + p) ^ 2 :=
    mul_le_mul_of_nonneg_right hdle (sq_nonneg _)
  have hbound3 : ((r : ℤ) + p) ^ 2 ≤ 4 * p * q := by
    nlinarith only [hdle, hri]
  have hbound4 : 4 * (p : ℤ) * ((r : ℤ) + p) ^ 2 ≤ 16 * p ^ 2 * q := by
    have := mul_le_mul_of_nonneg_left hbound3 (by positivity : 0 ≤ 4 * (p : ℤ))
    nlinarith only [this]
  have hbound5 : 16 * (p : ℤ) ^ 2 * q ≤ 16 * n * q := by
    have hsmalli : (p : ℤ) ^ 2 ≤ n := by
      have ht : (p : ℤ) * p ≤ n := by exact_mod_cast hsmall
      simpa only [pow_two] using ht
    have := mul_le_mul_of_nonneg_right hsmalli (by positivity : 0 ≤ 16 * (q : ℤ))
    nlinarith only [this]
  have hcsqi : 16 * (n : ℤ) * q < (c : ℤ) ^ 2 := by
    have ht : 16 * (n : ℤ) * q < (c : ℤ) * c := by exact_mod_cast hcsq
    simpa only [pow_two] using ht
  omega

end Hex.ECPP
