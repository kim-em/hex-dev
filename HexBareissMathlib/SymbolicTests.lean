
import HexBareissMathlib.Tactic
import Mathlib.Tactic.NormDet
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.ZMod.Basic

set_option hex.det.symbolic true

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
  simp only [hex_norm_det]
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
