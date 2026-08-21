/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std
public import Init.Grind.Ring.Field

public section

/-!
Shared exact scalar division.

The executable operations reuse the coefficient type's existing `/` and make
division by zero deterministic. Algebraic correctness is isolated in
`ExactDivLaws`; computational consumers need only the operations, while proof
consumers opt into the law package.

This module is coefficient-independent: it fixes the contract and the
cancellation lemmas that hold for every carrier, leaving carrier-specific
operations and instances (dense polynomials, matrices) to their consumers.
-/
namespace Hex

universe u

/-- A quotient operation is exact when multiplication by every nonzero right
factor can be undone by division by that factor. -/
class ExactDivLaws (R : Type u) [Zero R] [Mul R] [Div R] : Prop where
  /-- Right multiplication followed by division by a nonzero factor cancels. -/
  mul_div_cancel_right : ∀ a b : R, b ≠ 0 → (a * b) / b = a

namespace ExactDivLaws

variable {R : Type u}

/-- Exact division implies right cancellation by a nonzero factor. -/
theorem mul_right_cancel [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]
    {a b c : R} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hdiv := congrArg (fun x : R => x / c) h
  rw [ExactDivLaws.mul_div_cancel_right a c hc,
    ExactDivLaws.mul_div_cancel_right b c hc] at hdiv
  exact hdiv

/-- Exact division and commutative-ring laws rule out nonzero products
vanishing. -/
theorem mul_ne_zero [Lean.Grind.CommRing R] [Div R] [ExactDivLaws R]
    {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hzero
  have hdiv := congrArg (fun x : R => x / b) hzero
  have hzdiv : (0 : R) / b = 0 := by
    simpa [Lean.Grind.Semiring.zero_mul] using
      (ExactDivLaws.mul_div_cancel_right (0 : R) b hb)
  rw [ExactDivLaws.mul_div_cancel_right a b hb, hzdiv] at hdiv
  exact ha hdiv

end ExactDivLaws

variable {R : Type u}

/-- A nonzero element witnesses that a lightweight ring is nontrivial. -/
theorem one_ne_zero_of_nonzero {S : Type u} [Lean.Grind.CommRing S]
    {a : S} (ha : a ≠ 0) : (1 : S) ≠ 0 := by
  intro hone
  apply ha
  calc
    a = a * 1 := (Lean.Grind.Semiring.mul_one _).symm
    _ = a * 0 := by rw [hone]
    _ = 0 := Lean.Grind.Semiring.mul_zero _

/-- The additive inverse of one is nonzero in a nontrivial lightweight ring. -/
theorem negOne_ne_zero_of_one {S : Type u} [Lean.Grind.CommRing S]
    (h1 : (1 : S) ≠ 0) : (0 - 1 : S) ≠ 0 := by
  intro hzero
  apply h1
  calc
    1 = 0 - (0 - (1 : S)) := by grind
    _ = 0 - 0 := by rw [hzero]
    _ = 0 := by grind

/-- Total exact quotient wrapper. The zero denominator is a documented junk
input and returns zero. -/
@[expose]
def exactDiv [Zero R] [DecidableEq R] [Div R] (a b : R) : R :=
  if b = 0 then 0 else a / b

/-- Exact division by zero takes the stable junk branch. -/
@[simp, grind =]
theorem exactDiv_zero_right [Zero R] [DecidableEq R] [Div R] (a : R) :
    exactDiv a 0 = 0 := by
  simp [exactDiv]

/-- A nonzero exact quotient is the underlying quotient operation. -/
theorem exactDiv_eq_div_of_ne [Zero R] [DecidableEq R] [Div R]
    (a : R) {b : R} (hb : b ≠ 0) : exactDiv a b = a / b := by
  simp [exactDiv, hb]

/-- The wrapper cancels a nonzero exact right factor under `ExactDivLaws`. -/
@[simp]
theorem exactDiv_mul_right [Lean.Grind.CommRing R] [DecidableEq R] [Div R]
    [ExactDivLaws R] (a : R) {b : R} (hb : b ≠ 0) :
    exactDiv (a * b) b = a := by
  rw [exactDiv_eq_div_of_ne _ hb]
  exact ExactDivLaws.mul_div_cancel_right a b hb

/-- Natural powers by binary exponentiation, using only the executable `One`
and `Mul` operations. The association order is part of this law-free
computational definition; correctness consumers assume associative ring
multiplication. -/
@[expose]
def powNat [One R] [Mul R] (x : R) (n : Nat) : R :=
  if n = 0 then
    1
  else
    let y := powNat (x * x) (n / 2)
    if n % 2 = 0 then y else y * x
termination_by n
decreasing_by omega

/-- Powers distribute over multiplication in a lightweight commutative ring. -/
theorem mul_pow {S : Type u} [Lean.Grind.CommRing S]
    (a b : S) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by
      rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.pow_zero,
        Lean.Grind.Semiring.pow_zero]
      exact (Lean.Grind.Semiring.mul_one 1).symm
  | n + 1 => by
      rw [Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ,
        Lean.Grind.Semiring.pow_succ, mul_pow a b n]
      grind

/-- Raising a power to another power multiplies the two exponents. -/
theorem pow_mul {S : Type u} [Lean.Grind.Semiring S]
    (x : S) (m n : Nat) : x ^ (m * n) = (x ^ m) ^ n := by
  symm
  induction n with
  | zero => simp [Lean.Grind.Semiring.pow_zero]
  | succ n ih =>
      rw [Lean.Grind.Semiring.pow_succ, ih,
        ← Lean.Grind.Semiring.pow_add]
      congr 1

/-- Natural powers of a nonzero element stay nonzero in every nontrivial
exact-division ring. -/
theorem pow_ne_zero {S : Type u} [Lean.Grind.CommRing S] [Div S]
    [ExactDivLaws S] (h1 : (1 : S) ≠ 0) {a : S} (ha : a ≠ 0) :
    ∀ n : Nat, a ^ n ≠ 0
  | 0 => by
      simpa only [Lean.Grind.Semiring.pow_zero] using h1
  | n + 1 => by
      rw [Lean.Grind.Semiring.pow_succ]
      exact ExactDivLaws.mul_ne_zero (pow_ne_zero h1 ha n) ha

/-- The executable binary power agrees with the lightweight semiring power. -/
theorem powNat_eq_pow {S : Type u} [Lean.Grind.Semiring S]
    (x : S) (n : Nat) : powNat x n = x ^ n := by
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
      rw [powNat]
      by_cases hn : n = 0
      · subst n
        simp [Lean.Grind.Semiring.pow_zero]
      · rw [if_neg hn]
        have hlt : n / 2 < n :=
          Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2)
        rw [ih (n / 2) hlt (x * x)]
        have hdiv := Nat.mod_add_div n 2
        by_cases heven : n % 2 = 0
        · rw [if_pos heven, ← Lean.Grind.Semiring.pow_two, ← pow_mul]
          congr 1
          omega
        · rw [if_neg heven, ← Lean.Grind.Semiring.pow_two, ← pow_mul,
            ← Lean.Grind.Semiring.pow_succ]
          congr 1
          have hmod := Nat.mod_lt n (by decide : 0 < 2)
          omega

/-- The executable natural power of a nonzero element stays nonzero. -/
theorem powNat_ne_zero {S : Type u} [Lean.Grind.CommRing S] [Div S]
    [ExactDivLaws S] (h1 : (1 : S) ≠ 0) {a : S} (ha : a ≠ 0) (n : Nat) :
    powNat a n ≠ 0 := by
  rw [powNat_eq_pow]
  exact pow_ne_zero h1 ha n

/-- Brown's scalar update `x^n / y^(n-1)`, with the same total zero behavior
as `exactDiv`. -/
@[expose]
def divExp [Zero R] [DecidableEq R] [One R] [Mul R] [Div R]
    (x y : R) (n : Nat) : R :=
  exactDiv (powNat x n) (powNat y (n - 1))

/-- Integer Euclidean division is exact on nonzero right multiples. -/
instance instExactDivLawsInt : ExactDivLaws Int where
  mul_div_cancel_right := Int.mul_ediv_cancel

/-- Every `Lean.Grind.Field` supplies the exact-division law. -/
instance instExactDivLawsField {K : Type u} [Lean.Grind.Field K] :
    ExactDivLaws K where
  mul_div_cancel_right a b hb := by
    rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
      Lean.Grind.Field.mul_inv_cancel hb, Lean.Grind.Semiring.mul_one]

/-! Instance-contract check for the integer coefficient tower. -/

example : ExactDivLaws Int := inferInstance

/-! Value-level pins for the total quotient and binary-power helpers. -/

#guard powNat (3 : Int) 5 = 243

#guard exactDiv (7 : Int) 0 = 0

#guard divExp (4 : Int) 2 3 = 16

end Hex
