/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Algebra.Ring.GrindInstances
public import HexPoly

public section

/-!
Mathlib ring structures for executable carriers.

The computational libraries carry `Lean.Grind.CommRing` instances, while the
Mathlib bridge theorems take Mathlib's `CommRing`. `commRingOfGrind` builds the
latter from the former, keeping every executable operation: addition,
multiplication, negation, subtraction, the numeral and cast maps, scalar
multiplications, and the executable power. `toGrind_commRingOfGrind` records
that the resulting `Lean.Grind.CommRing` reduct is the original instance, which
is what lets a Mathlib-side theorem stated over `[CommRing R]` be used against a
goal stated over `[Lean.Grind.CommRing R]`.

That round trip is an equation rather than a definitional identity: Mathlib's
`Semiring.toGrindSemiring` picks its numeral instances branchwise at `0`, `1`
and `n + 2`, which agrees with an arbitrary `Lean.Grind.Semiring.ofNat` only up
to `Lean.Grind.Semiring.ofNat_eq_natCast`. Every other field is a projection of
the original instance.

Executable `Hex.DensePoly` (hence `Hex.ZPoly`), `Hex.ZMod64` and the executable
finite-field polynomials have no global Mathlib `CommRing` instance and are all
covered by this one transport; `denseCommRing` names the dense-polynomial case.
The private structure in `HexResultantMathlib/Specialize.lean` uses `npowRec`
and is not a substitute: it replaces the executable power.
-/

namespace HexPolyMathlib

universe u

section Transport

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

/-- Mathlib's `CommRing` structure on a type carrying `Lean.Grind.CommRing`,
with every operation taken from that instance. -/
@[instance_reducible, expose] def commRingOfGrind {R : Type u} [s : Lean.Grind.CommRing R] :
    CommRing R :=
  { s with
    zero_add := Lean.Grind.AddCommMonoid.zero_add
    right_distrib := Lean.Grind.Semiring.right_distrib
    mul_zero := Lean.Grind.Semiring.mul_zero
    one_mul := Lean.Grind.Semiring.one_mul
    nsmul := fun n a => n • a
    nsmul_zero := fun a => by
      rw [Lean.Grind.Semiring.nsmul_eq_natCast_mul, Lean.Grind.Semiring.natCast_zero,
        Lean.Grind.Semiring.zero_mul]
    nsmul_succ := fun n a => by
      rw [Lean.Grind.Semiring.nsmul_eq_natCast_mul, Lean.Grind.Semiring.nsmul_eq_natCast_mul,
        Lean.Grind.Semiring.natCast_succ, Lean.Grind.Semiring.right_distrib,
        Lean.Grind.Semiring.one_mul]
    npow := fun n a => a ^ n
    npow_zero := Lean.Grind.Semiring.pow_zero
    npow_succ := fun n a => Lean.Grind.Semiring.pow_succ a n
    zsmul := fun z a => z • a
    zsmul_zero' := fun a => by
      rw [show ((0 : Int)) = ((0 : Nat) : Int) from rfl,
        Lean.Grind.Ring.zsmul_natCast_eq_nsmul,
        Lean.Grind.Semiring.nsmul_eq_natCast_mul, Lean.Grind.Semiring.natCast_zero,
        Lean.Grind.Semiring.zero_mul]
    zsmul_succ' := fun n a => by
      rw [Lean.Grind.Ring.zsmul_natCast_eq_nsmul, Lean.Grind.Ring.zsmul_natCast_eq_nsmul,
        Lean.Grind.Semiring.nsmul_eq_natCast_mul, Lean.Grind.Semiring.nsmul_eq_natCast_mul,
        Lean.Grind.Semiring.natCast_succ, Lean.Grind.Semiring.right_distrib,
        Lean.Grind.Semiring.one_mul]
    zsmul_neg' := fun n a => by
      rw [show Int.negSucc n = -((n + 1 : Nat) : Int) from rfl, Lean.Grind.Ring.neg_zsmul]
    natCast := Nat.cast
    natCast_zero := Lean.Grind.Semiring.natCast_zero
    natCast_succ n := Lean.Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Lean.Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Lean.Grind.Ring.intCast_neg,
        Lean.Grind.Ring.intCast_natCast_add_one, Lean.Grind.Semiring.natCast_succ] }

end Transport

/-- The `Lean.Grind.CommRing` reduct of `commRingOfGrind` is the instance it was
built from. Rewriting with this equation moves a Mathlib-side theorem stated over
`[CommRing R]` onto a goal stated over the executable instance. -/
theorem toGrind_commRingOfGrind {R : Type u} [s : Lean.Grind.CommRing R] :
    @CommRing.toGrindCommRing R commRingOfGrind = s := by
  unfold CommRing.toGrindCommRing Ring.toGrindRing Semiring.toGrindSemiring
  dsimp only
  congr 1
  congr 1
  congr 1
  · funext k
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
        exact congrArg (@OfNat.mk R (k + 2))
          (Lean.Grind.Semiring.ofNat_eq_natCast (k + 2)).symm
  · exact proof_irrel_heq _ _
  · exact proof_irrel_heq _ _

/-- A Mathlib `CommRing` structure whose `Lean.Grind.CommRing` reduct is the
carrier's executable instance. A bridge theorem stated over `[CommRing R]` can be
moved onto a goal stated over the executable instance exactly when this holds.

The default proof discharges the field-by-field comparison: every field is a
projection of the same instance except the numerals, which agree by
`Lean.Grind.Semiring.ofNat_eq_natCast`. -/
class GrindReduct (R : Type u) [s : Lean.Grind.CommRing R] [inst : CommRing R] : Prop where
  /-- The Mathlib structure reduces to the executable instance. -/
  toGrind_eq : @CommRing.toGrindCommRing R inst = s := by
    unfold CommRing.toGrindCommRing Ring.toGrindRing Semiring.toGrindSemiring
    dsimp only
    congr 1
    congr 1
    congr 1
    · funext k
      match k with
      | 0 => rfl
      | 1 => rfl
      | k + 2 =>
          exact congrArg OfNat.mk
            (Lean.Grind.Semiring.ofNat_eq_natCast (k + 2)).symm
    · exact proof_irrel_heq _ _
    · exact proof_irrel_heq _ _

instance instGrindReductOfGrind {R : Type u} [s : Lean.Grind.CommRing R] :
    @GrindReduct R s commRingOfGrind :=
  @GrindReduct.mk R s commRingOfGrind toGrind_commRingOfGrind

/-- Mathlib's `CommRing` structure on the executable dense polynomials, with the
executable operations. This covers `Hex.ZPoly` and the executable finite-field
polynomials, which are `Hex.DensePoly` at `Int` and at `Hex.ZMod64 p`. -/
@[instance_reducible, expose] def denseCommRing {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] :
    CommRing (Hex.DensePoly R) :=
  commRingOfGrind

example : CommRing (Hex.DensePoly Int) := denseCommRing

example : CommRing (Hex.DensePoly Rat) := denseCommRing

end HexPolyMathlib
