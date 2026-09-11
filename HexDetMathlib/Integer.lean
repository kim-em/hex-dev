/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Basic
public import HexBareissMathlib

public section

/-!
The integer arm.

An integer recipe maps the entries through `toInt`, runs the integer backend, and
maps the answer back through `ofInt`. Correctness is the Leibniz sum commuting
with `toInt`, which is `RingHom.map_det` once the preservation laws are packaged
as a ring homomorphism, followed by the left inverse law returning the answer to
the carrier.

Preservation of negation is not a separate hypothesis: a map preserving zero,
one, addition and multiplication is a ring homomorphism, and ring homomorphisms
preserve negation. Only the `ofInt ∘ toInt` direction of the inverse law is
consumed, since the answer travels in that direction. Neither omission weakens
the contract: a unital ring homomorphism into `Int` is surjective, because its
image contains `1` and is closed under negation and addition, so the other
inverse direction and the ring behaviour of `ofInt` follow. The shipped `Int`
recipe uses identity maps, where every one of these laws is `rfl`.
-/

namespace HexDetMathlib

open Hex.Det

universe u

variable {R : Type u} [Lean.Grind.CommRing R] {n : Nat}

/-- Carrying the entries into `Int` and transporting to Mathlib is the same as
transporting and mapping entrywise. -/
theorem matrixEquiv_toIntMatrix (toInt : R → Int) (A : Hex.Matrix R n n) :
    HexMatrixMathlib.matrixEquiv (toIntMatrix toInt A) =
      (HexMatrixMathlib.matrixEquiv A).map toInt := by
  ext i j
  rw [HexMatrixMathlib.matrixEquiv_apply, Matrix.map_apply,
    HexMatrixMathlib.matrixEquiv_apply, toIntMatrix,
    ← Hex.Matrix.getElem_pair_eq_nested A i j]
  exact Hex.Matrix.getElem_ofFn (fun i j => toInt A[(i, j)]) i j

/-- The integer arm computes the reference determinant when its representation
maps preserve the ring operations and `ofInt` undoes `toInt`. -/
theorem integerDet_eq_det (toInt : R → Int) (ofInt : Int → R)
    (hinv : ∀ a : R, ofInt (toInt a) = a)
    (hzero : toInt 0 = 0) (hone : toInt 1 = 1)
    (hadd : ∀ a b : R, toInt (a + b) = toInt a + toInt b)
    (hmul : ∀ a b : R, toInt (a * b) = toInt a * toInt b)
    (A : Hex.Matrix R n n) :
    integerDet toInt ofInt A = Hex.Matrix.det A := by
  let _ : CommRing R := HexPolyMathlib.commRingOfGrind
  let f : R →+* Int :=
    { toFun := toInt, map_one' := hone, map_mul' := hmul
      map_zero' := hzero, map_add' := hadd }
  have hdet : Hex.Matrix.bareiss (toIntMatrix toInt A) = toInt (Hex.Matrix.det A) := by
    rw [HexMatrixMathlib.bareiss_eq_mathlib_det, matrixEquiv_toIntMatrix,
      show (HexMatrixMathlib.matrixEquiv A).map toInt =
        (HexMatrixMathlib.matrixEquiv A).map f from rfl,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det f, ← HexMatrixMathlib.det_eq A]
    rfl
  rw [integerDet, hdet, hinv]

/-- The integer recipe is lawful under those laws. -/
theorem lawfulPolicy_integer (toInt : R → Int) (ofInt : Int → R)
    (hinv : ∀ a : R, ofInt (toInt a) = a)
    (hzero : toInt 0 = 0) (hone : toInt 1 = 1)
    (hadd : ∀ a b : R, toInt (a + b) = toInt a + toInt b)
    (hmul : ∀ a b : R, toInt (a * b) = toInt a * toInt b) :
    LawfulPolicy (Policy.integer toInt ofInt IntArm.bareiss) :=
  lawfulPolicy_of_eval_eq fun A => integerDet_eq_det toInt ofInt hinv hzero hone hadd hmul A

end HexDetMathlib
