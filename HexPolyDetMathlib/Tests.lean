/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import Mathlib.Tactic.NormDet
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic


example (x : Int) : Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by det

theorem symbolicDet {R : Type} [CommRing R] [CharZero R] (x : R) :
    Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by det

example (x : Rat) : Matrix.det !![x / 2, 1; 1, x / 3] = x ^ 2 / 6 - 1 := by det
example (x : Rat) : Matrix.det !![x + 1 / 2, 1; 1, x - 1 / 3] =
    x ^ 2 + x / 6 - 7 / 6 := by det
example (x y : Rat) : Matrix.det !![x / y, 1; 1, x / y] = (x / y) ^ 2 - 1 := by det
example (x y : Int) : Matrix.det !![x, y; x + x, y + y] = 0 := by det
example (x : Int) : Matrix.det !![0, x; x, 1] = -x ^ 2 := by det

example (x : Int) : x ^ 2 - 1 = Matrix.det !![x, 1; 1, x] := by det
example (x : Int) : Matrix.det (Matrix.ofArray (m := 2) (n := 2) #[x, 1, 1, x] rfl) =
    x ^ 2 - 1 := by det
example (x : Int) : Matrix.det (fun i j : Fin 2 => if i = j then x else 1) = x ^ 2 - 1 := by det
example (x : Int) : Matrix.det !![x, 1; 1, x] = (det% !![x, 1; 1, x]).value :=
  (det% !![x, 1; 1, x]).proof
example (x : Rat) : Matrix.det (!![x / 2, 1; 1, x / 3] : Matrix (Fin 2) (Fin 2) Rat) =
    (det% (!![x / 2, 1; 1, x / 3] : Matrix (Fin 2) (Fin 2) Rat)).value :=
  (det% (!![x / 2, 1; 1, x / 3] : Matrix (Fin 2) (Fin 2) Rat)).proof
example (x : Int) : Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by
  simp only [Hex.normPolyDet]
  ring

/-- info: 'symbolicDet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symbolicDet

-- Even a local equality does not change the independent-atom computation.
example (x : Int) (h : x = 0) : Matrix.det !![x] = 0 := by
  fail_if_success det
  simpa only [Matrix.det_fin_one, Matrix.of_apply, Matrix.cons_val_zero] using h

-- A right-hand side introducing an atom outside the matrix must decline.
example (x y : Int) (h : Matrix.det !![x, 1; 1, x] = y) :
    Matrix.det !![x, 1; 1, x] = y := by
  fail_if_success det
  exact h

-- The composed fallback remains available on unsupported positive characteristic.
example (x : ZMod 3) : Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by
  det

-- Coefficients cancel before elimination, although the batch contains atoms.
example (x : Int) : Matrix.det !![x - x, 1; 1, x - x] = -1 := by det
example (x : Int) : Matrix.det (fun (_ _ : Fin 0) => x) = 1 := by det
example (x : Rat) : Matrix.det !![x / 0, 1; 1, x] = -1 := by det
example (x : Rat) : Matrix.det !![x, 1; 1, x] = (det% !![x, 1; 1, x]).value :=
  (det% !![x, 1; 1, x]).proof
example {R : Type} [CommRing R] [CharZero R] (x : R) :
    Matrix.det !![x, 1; 1, x] = (det% !![x, 1; 1, x]).value :=
  (det% !![x, 1; 1, x]).proof

namespace ClosedAlgebraic
abbrev K := QuadraticAlgebra Rat 2 0
@[irreducible] def α : K := QuadraticAlgebra.omega

theorem square : α ^ 2 = 2 := by
  rw [α, pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl

theorem polynomial : Matrix.det !![α, 1; 2, α] = α ^ 2 - 2 := by det

example : Matrix.det !![α, 1; 2, α] = 0 := by
  fail_if_success det
  rw [polynomial, square, sub_self]
end ClosedAlgebraic

-- Positive-characteristic kernel probes are documented non-tests until both
-- #10255 and #10257 land. In particular X^3-X in characteristic 3 must be
-- treated as a nonzero polynomial, and a composite modulus must decline.

-- Malformed list encodings cannot reach the denotation theorem as certificates.
example : Hex.Matrix.checkDetPolyList (HexMatrixMathlib.DetPoly.Polynomial.ops 1)
    1 [[[([0], (1 : Int)), ([0], 1)]]]
    (.triangular [] [[[([0], 1)]]] [([0], 2)]) = false := by decide +kernel
example : Hex.Matrix.checkDetPolyList (HexMatrixMathlib.DetPoly.Polynomial.ops 1)
    1 [[[([0, 0], (1 : Int))]]]
    (.triangular [] [[[([0], 1)]]] [([0], 1)]) = false := by decide +kernel
example : Hex.Matrix.checkDetPolyList (HexMatrixMathlib.DetPoly.Polynomial.ops 1)
    1 [[[([0], (1 : Int))]]]
    (.singular [[]]) = false := by decide +kernel

-- Closed scalar powers are bounded before the rational evaluator sees them.
example : True := by
  run_tac
    let two ← Lean.Meta.mkNumeral (Lean.mkConst ``Rat) 2
    let e ← Lean.Meta.mkAppM ``HPow.hPow #[two, Lean.mkNatLit 65]
    match ← (HexMatrixMathlib.DetPoly.Normalize.scalarBound e).run with
    | .error _ => pure ()
    | .ok _ => throwError "expected a scalar exponent budget decline"
  trivial

example : True := by
  run_tac
    let two ← Lean.Meta.mkNumeral (Lean.mkConst ``Rat) 2
    let e ← Lean.Meta.mkAppM ``HPow.hPow #[two, Lean.mkNatLit 64]
    let e ← Lean.Meta.mkAppM ``HPow.hPow #[e, Lean.mkNatLit 64]
    match ← (HexMatrixMathlib.DetPoly.Normalize.scalarBound e).run with
    | .error _ => pure ()
    | .ok _ => throwError "expected a scalar coefficient bit budget decline"
  trivial

namespace HexPolyDetTests

open Lean Elab Tactic Meta in
/-- Regression helper requiring the polynomial certificate, without the small
formula route or Mathlib fallback. -/
elab "certificate_det" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (A, rhs, reverse) := HexMatrixMathlib.Det.detTarget? target |
    throwError "expected a determinant equation"
  match ← HexMatrixMathlib.DetPoly.Frontend.compute A rhs with
  | .success p => closeMainGoal `certificate_det (← if reverse then mkEqSymm p.proof else pure p.proof)
  | .declined msg | .notApplicable msg => throwError "certificate required: {msg}"

-- The target need not be a domain or characteristic zero.
theorem generic4 {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      x ^ 4 - 3 * x ^ 2 + 1 := by certificate_det

-- The producer divides by the nonconstant pivot x in these certificates.
theorem division3 (x : Int) :
    Matrix.det !![x, 1, 0; 1, x, 1; 0, 1, x] = x ^ 3 - 2 * x := by certificate_det

theorem rational4 (x : Rat) :
    Matrix.det !![x / 2, 1, 0, 0; 1, x / 2, 1, 0; 0, 1, x / 2, 1; 0, 0, 1, x / 2] =
      x ^ 4 / 16 - 3 * x ^ 2 / 4 + 1 := by certificate_det

theorem singular4 (x y : Int) :
    Matrix.det !![x, y, 1, 0; 0, x, y, 1; x, y, 1, 0; 1, 0, x, y] = 0 := by certificate_det

theorem term4 (x : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      (det% !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x]).value :=
  (det% !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x]).proof

example (x : Int) : True := by
  let y := x + 1
  have : Matrix.det !![y, 1, 0, 0; 1, y, 1, 0; 0, 1, y, 1; 0, 0, 1, y] =
      y ^ 4 - 3 * y ^ 2 + 1 := by certificate_det
  trivial

example (x : ZMod 6) :
    Matrix.det !![x, 0, 0, 0; 0, x, 0, 0; 0, 0, x, 0; 0, 0, 0, x] =
      x ^ 4 := by certificate_det

-- Closed formulas do not require CharZero, even for composite characteristic.
example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1, 0; 1, x, 1; 0, 1, x] = x ^ 3 - 2 * x := by det

-- Definitions discovered within the literal-unfolding budget use the general
-- closed formulas with the original matrix as argument.
def symbolicMatrix (x : Int) : Matrix (Fin 2) (Fin 2) Int := !![x, 1; 1, x]
example (x : Int) : (symbolicMatrix x).det = x ^ 2 - 1 := by det
example (x : Int) : (symbolicMatrix x).det = (det% (symbolicMatrix x)).value :=
  (det% (symbolicMatrix x)).proof

-- A new target atom forces a polynomial decline; the composed fallback closes it.
example (x y : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      x ^ 4 - 3 * x ^ 2 + 1 + y - y := by det

-- Numeric delegation and its Hex simp fallback retain their original behavior.
example (y : Int) (h : y = -2) : Matrix.det !![(1 : Int), 2; 3, 4] = y := by
  det
  exact h.symm

/-- info: 'HexPolyDetTests.generic4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generic4
/-- info: 'HexPolyDetTests.rational4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational4
/-- info: 'HexPolyDetTests.singular4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms singular4
/-- info: 'HexPolyDetTests.term4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms term4

end HexPolyDetTests
