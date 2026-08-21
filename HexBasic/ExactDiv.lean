/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

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

Nothing here shadows a Mathlib root name, and that is deliberate. `HexBasic`
sits below the whole graph, so a declaration `Hex.foo` added here is in scope
for every `Hex*Mathlib` file wherever `open Hex` is in effect, and a bare `foo`
in that scope is an ambiguous term when Mathlib also defines `_root_.foo`.
That rules out hosting the binary-power helpers here: `Hex.mul_pow`,
`Hex.pow_mul`, and `Hex.pow_ne_zero` all collide that way, and
`HexGFqMathlib/Primitivity.lean` is a live site. They stay with their
Brown-recurrence consumer in `HexResultant/ExactDiv.lean`, along with `powNat`
and `divExp`, which nothing below `hex-resultant` needs.
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

/-! Value-level pin for the total quotient. -/

#guard exactDiv (7 : Int) 0 = 0

end Hex
