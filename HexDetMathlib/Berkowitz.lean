/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Basic
public import HexCharPolyMathlib

public section

/-!
The Berkowitz arm.

`HexCharPolyMathlib.coeff_zero_charPoly` gives
`(charPoly A).coeff 0 = (-1) ^ n * det A`. Multiplying by `(-1) ^ n` and
cancelling the square recovers the determinant, with no nontriviality,
invertibility or characteristic restriction, so this arm serves rings with zero
divisors and the trivial ring. Both signs matter: in odd dimensions the sign is
`-1`, and dropping it would return the determinant's negation.
-/

namespace HexDetMathlib

open Hex.Det

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

omit [DecidableEq R] in
/-- `(-1) ^ n` squares to one in any commutative ring. -/
theorem negOne_pow_sq (n : Nat) : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  induction n with
  | zero => rw [Lean.Grind.Semiring.pow_zero, Lean.Grind.Semiring.mul_one]
  | succ k ih =>
      rw [Lean.Grind.Semiring.pow_succ]
      grind

/-- The signed constant coefficient of the characteristic polynomial is the
reference determinant. -/
theorem berkowitzDet_eq_det (A : Hex.Matrix R n n) :
    berkowitzDet A = Hex.Matrix.det A := by
  have hcoeff := @HexCharPolyMathlib.coeff_zero_charPoly R
    HexPolyMathlib.commRingOfGrind _ n A
  rw [HexPolyMathlib.toGrind_commRingOfGrind] at hcoeff
  show (-1 : R) ^ n * (Hex.Matrix.charPoly A).coeff 0 = Hex.Matrix.det A
  rw [hcoeff, ← Lean.Grind.Semiring.mul_assoc, negOne_pow_sq,
    Lean.Grind.Semiring.one_mul]

omit [DecidableEq R] in
/-- The Berkowitz recipe is lawful over every commutative ring with decidable
equality. -/
theorem lawfulPolicy_berkowitz (deq : DecidableEq R) :
    LawfulPolicy (Policy.berkowitz deq) :=
  lawfulPolicy_of_eval_eq fun A => @berkowitzDet_eq_det R _ deq _ A

end HexDetMathlib
