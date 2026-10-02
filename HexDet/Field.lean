/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDet.Basic
public import HexPolyFp.PrimeField

public section

/-!
Field recipes.

`Rat` and the prime-modulus machine-word residues `Hex.ZMod64 p` both select
Bareiss through their own division. `Hex.Det.guardQuot` makes that division
total, which is what the exact-quotient contract of `Hex.Matrix.bareissWith`
asks for; the companion discharges it from the field's cancellation law.

Forward elimination with row pivoting is the other arm this row will offer, but
a determinant-specific elimination does not exist below dispatch yet:
`Hex.Matrix.rowReduce` returns a reduced form and a transform without the
determinant of that transform, and multiplying its normalized diagonal is not a
determinant algorithm. So `Hex.Det.FieldArm` offers only Bareiss, and the
dimension region separating the two arms arrives with the measurement that sets
it.
-/

namespace Hex.Det

/-- Division of machine-word residues by a nonzero residue modulo a prime is
exact. The `Lean.Grind.Field` route cannot supply this to instance search: the
field instance is assembled by tactic, so its division parent does not unfold to
`HexPolyFp`'s `Div (Hex.ZMod64 p)` at instances transparency. Stating it against
that division is what makes the dense-polynomial recipe resolve over
`Hex.FpPoly p`. -/
instance instExactDivLawsZMod64 {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    Hex.ExactDivLaws (ZMod64 p) where
  mul_div_cancel_right a b hb := by
    have hinv : b * b⁻¹ = (1 : ZMod64 p) := by
      rw [Lean.Grind.CommSemiring.mul_comm]
      exact ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hb
    show a * b * b⁻¹ = a
    rw [Lean.Grind.Semiring.mul_assoc, hinv, Lean.Grind.Semiring.mul_one]

/-- The recipe for an arbitrary field: Bareiss through the field's division.
This is an explicit constructor rather than a blanket instance, so importing it
cannot displace a carrier's own recipe. -/
@[expose] def fieldPolicy {F : Type u} [Lean.Grind.Field F] [DecidableEq F] : Policy F :=
  .field inferInstance (· / ·) .bareiss

/-- The rational recipe. -/
instance instDetOpsRat : DetOps Rat where
  policy := fieldPolicy

/-- The prime-residue recipe, over the field structure `HexPolyFp.PrimeField`
builds from the prime modulus. -/
instance instDetOpsZMod64 {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    DetOps (ZMod64 p) where
  policy := fieldPolicy

example : (DetOps.policy (R := Rat)).arm = Arm.bareiss := rfl

example {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    (DetOps.policy (R := ZMod64 p)).arm = Arm.bareiss := rfl

end Hex.Det
