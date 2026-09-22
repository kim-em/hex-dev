/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import Mathlib.Tactic.NormDet
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Field.ZMod


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
example : Matrix.det !![(1 : Int), 2; 3, 4] = -2 := by simp only [Hex.normPolyDet]

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

-- The Hex small-formula route handles positive characteristic.
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
formula route. -/
elab "certificate_det" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (A, rhs, reverse) := HexMatrixMathlib.Det.detTarget? target |
    throwError "expected a determinant equation"
  match ← HexMatrixMathlib.DetPoly.Frontend.compute A rhs with
  | .success p => closeMainGoal `certificate_det (← if reverse then mkEqSymm p.proof else pure p.proof)
  | .declined msg | .notApplicable msg => throwError "certificate required: {msg}"

open Lean Elab Tactic Meta in
elab "certificate_declines " reason:str : tactic => withMainContext do
  let some (A, rhs, _) := HexMatrixMathlib.Det.detTarget? (← getMainTarget) |
    throwError "expected a determinant equation"
  match ← HexMatrixMathlib.DetPoly.Frontend.compute A rhs with
  | .declined msg =>
    unless ((← msg.toString).splitOn reason.getString).length > 1 do
      throwError "unexpected decline: {msg}"
  | _ => throwError "expected a certificate decline"

open MvPolynomial in
theorem residue4 : Matrix.det
    (!![X 0, 1, 0, 0; 1, X 0, 0, 0; 0, 0, X 1, 1; 0, 0, 1, X 1] :
      Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 2) (ZMod 3))) =
        (X 0 ^ 2 - 1) * (X 1 ^ 2 - 1) := by certificate_det

open MvPolynomial in
theorem residueFrobenius : Matrix.det
    (!![X 0 ^ 3 - X 0, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
      Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 1) (ZMod 3))) = X 0 ^ 3 - X 0 := by
  certificate_det

example (x : ZMod 3) : Matrix.det
    !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] = x ^ 4 + 1 := by
  det

example (x : ZMod 3) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, x, 1; 0, 0, 1, x] =
    (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, x, 1; 0, 0, 1, x]).value :=
  (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, x, 1; 0, 0, 1, x]).proof

example (x : ZMod 2) : Matrix.det !![x, x, 0; x, 0, x; 0, x, x] = 0 := by
  certificate_det

example (x : ZMod 3) : Matrix.det !![0, x; x, 1] = -x ^ 2 := by certificate_det

-- Polynomial replay must not replace a formal polynomial by its function on the field.
example (x : ZMod 3) : True := by
  fail_if_success have : Matrix.det !![x ^ 3 - x] = 0 := by certificate_det
  trivial

-- Canonical residue bounds and structural data are checked before denotation.
example : Hex.Matrix.checkDetPolyList (Hex.PolyDet.opsMod 3 1)
    1 [[[([1], 1)]]] (.triangular [] [[[([0], 1)]]] [([1], 1)]) = true := by decide +kernel
example : Hex.Matrix.checkDetPolyList (Hex.PolyDet.opsMod 3 1)
    1 [[[([1], 4)]]] (.triangular [] [[[([0], 1)]]] [([1], 1)]) = false := by decide +kernel
example : Hex.Matrix.checkDetPolyList (Hex.PolyDet.opsMod 3 1)
    1 [[[([1], 1)]]] (.triangular [] [[[([0], 3)]]] [([1], 1)]) = false := by decide +kernel
example : Hex.Matrix.checkDetPolyList (Hex.PolyDet.opsMod 3 1)
    1 [[[([1], 1)]]] (.singular [[]]) = false := by decide +kernel

/-- info: 'HexPolyDetTests.residue4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms residue4
/-- info: 'HexPolyDetTests.residueFrobenius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms residueFrobenius

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

example (x y z : Rat) : True := by
  run_tac
    let e ← Lean.Elab.Term.elabTerm
      (← `($(Lean.mkIdent `x) / 2 + $(Lean.mkIdent `y) / 2 + $(Lean.mkIdent `z) / 2)) none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    let .ok r ← (HexMatrixMathlib.DetPoly.Normalize.expression e).run |
      throwError "normalization failed"
    unless r.scale == 2 do throwError "repeated denominators should share one scale"
    let .ok (s, _) ← (HexMatrixMathlib.DetPoly.Normalize.row #[e, e, e, e]).run |
      throwError "row normalization failed"
    unless s == 2 do throwError "row denominators should share one scale"
  trivial

theorem singular4 (x y : Int) :
    Matrix.det !![x, y, 1, 0; 0, x, y, 1; x, y, 1, 0; 1, 0, x, y] = 0 := by certificate_det

theorem term4 (x : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      (det% !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x]).value :=
  (det% !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x]).proof

theorem rationalTerm4 (x : Rat) :
    Matrix.det !![x / 2, 1, 0, 0; 1, x / 2, 1, 0; 0, 1, x / 2, 1; 0, 0, 1, x / 2] =
      (det% !![x / 2, 1, 0, 0; 1, x / 2, 1, 0; 0, 1, x / 2, 1; 0, 0, 1, x / 2]).value :=
  (det% !![x / 2, 1, 0, 0; 1, x / 2, 1, 0; 0, 1, x / 2, 1; 0, 0, 1, x / 2]).proof

example (x : Rat) : (det% !![x, 0, 0, 0; 0, x, 0, 0; 0, 0, x, 0; 0, 0, 0, x]).value =
    x ^ 4 := by ring

example (x : Int) : Matrix.det (fun i j : Fin 4 => x + if i = j then 1 else 0) =
    4 * x + 1 := by certificate_det

example (x : Int) : Matrix.det (Matrix.ofArray (m := 4) (n := 4)
    #[x, 1, 0, 0, 1, x, 1, 0, 0, 1, x, 1, 0, 0, 1, x] rfl) =
    x ^ 4 - 3 * x ^ 2 + 1 := by certificate_det

example (x : Int) : x ^ 4 - 3 * x ^ 2 + 1 =
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] := by certificate_det

example (x : Int) : True := by
  let y := x + 1
  have : Matrix.det !![y, 1, 0, 0; 1, y, 1, 0; 0, 1, y, 1; 0, 0, 1, y] =
      y ^ 4 - 3 * y ^ 2 + 1 := by certificate_det
  trivial

example (x : ZMod 6) :
    Matrix.det !![x, 0, 0, 0; 0, x, 0, 0; 0, 0, x, 0; 0, 0, 0, x] =
      x ^ 4 := by
  certificate_det

-- Integer replay remains available when a residue domain is unavailable.
-- A characteristic-reduced conversion can still disagree with integer replay.
example (x : ZMod 6) :
    Matrix.det !![x - 1, 0, 0, 0; 0, x, 0, 0; 0, 0, x, 0; 0, 0, 0, x] =
      (x - 1) * x ^ 3 := by
  certificate_declines "entry (0, 0)"
  det

example {R : Type} [CommRing R] [CharP R 3] (x : R) :
    Matrix.det !![x, 0, 0, 0; 0, x, 0, 0; 0, 0, x, 0; 0, 0, 0, x] = x ^ 4 := by
  certificate_det

-- Closed formulas do not require CharZero, even for composite characteristic.
example {R : Type} [CommRing R] (x : R) :
    Matrix.det !![x, 1, 0; 1, x, 1; 0, 1, x] = x ^ 3 - 2 * x := by det

-- Definitions discovered within the literal-unfolding budget use the general
-- closed formulas with the original matrix as argument.
def symbolicMatrix (x : Int) : Matrix (Fin 2) (Fin 2) Int := !![x, 1; 1, x]
example (x : Int) : (symbolicMatrix x).det = x ^ 2 - 1 := by det
example (x : Int) : (symbolicMatrix x).det = (det% (symbolicMatrix x)).value :=
  (det% (symbolicMatrix x)).proof

-- The Hex structural formula can compare a target containing a canceled atom.
example (x y : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x] =
      x ^ 4 - 3 * x ^ 2 + 1 + y - y := by det

-- Numeric delegation may still normalize using a Hex certificate.
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

#print axioms Hex.PolyDet.check_of_ok
#print axioms HexPolyDetTests.rationalTerm4

namespace RowFactorTests

-- A local multiplication unrelated to the ring operation must decline.
example (x : Int) : True := by
  letI : HMul Int Int Int := ⟨fun a b => a + b⟩
  let A : Matrix (Fin 4) (Fin 4) Int :=
    !![1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 1 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← Lean.Meta.getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value?
      | throwError "row-factor instance test lost its local literal"
    let some lit ← HexMatrixMathlib.Literal.literal? a (allowOpen := true)
      | throwError "row-factor instance test did not recognize its literal"
    if (← HexPolyDetMathlib.RowFactor.compute? a lit none).isSome then
      throwError "row-factor shortcut accepted a non-ring multiplication"
  trivial

-- A factor of the wrong type must decline without an application error.
example (x : Nat) : True := by
  letI : HMul Int Nat Int := ⟨fun a b => a + (b : Int)⟩
  let A : Matrix (Fin 4) (Fin 4) Int :=
    !![(1 : Int) * x, (0 : Int) * x, (0 : Int) * x, (0 : Int) * x;
      (0 : Int) * x, (1 : Int) * x, (0 : Int) * x, (0 : Int) * x;
      (0 : Int) * x, (0 : Int) * x, (1 : Int) * x, (0 : Int) * x;
      (0 : Int) * x, (0 : Int) * x, (0 : Int) * x, (1 : Int) * x]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← Lean.Meta.getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing local literal"
    let some lit ← HexMatrixMathlib.Literal.literal? a (allowOpen := true)
      | throwError "mixed-type test did not recognize its literal"
    if (← HexPolyDetMathlib.RowFactor.compute? a lit none).isSome then
      throwError "row-factor shortcut accepted mixed-type multiplication"
  trivial

example (x : Int) : True := by
  let A : Matrix (Fin 4) (Fin 4) Int :=
    !![1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 1 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← Lean.Meta.getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing local literal"
    let some lit ← HexMatrixMathlib.Literal.literal? a (allowOpen := true)
      | throwError "metavariable test did not recognize its literal"
    let rhs ← Lean.Meta.mkFreshExprMVar (Lean.mkConst ``Int)
    if (← HexPolyDetMathlib.RowFactor.compute? a lit (some rhs)).isSome then
      throwError "row-factor shortcut accepted an unresolved target"
    if ← rhs.mvarId!.isAssigned then throwError "row-factor shortcut assigned the target"
  trivial

-- Arbitrary factors, arbitrary universe, and no characteristic restriction.
theorem generic {R : Type u} [CommRing R] (a b c d : R) :
    Matrix.det !![(-3) * a, (-2) * a, (-3) * a, 3 * a;
      (-1) * b, 1 * b, (-3) * b, (-1) * b;
      3 * c, 3 * c, (-2) * c, (-1) * c;
      3 * d, 2 * d, (-1) * d, (-1) * d] = (-26) * a * b * c * d := by
  det

theorem term (x : Rat) :
    Matrix.det !![1 * x, 0 * x, 0 * x, 0 * x;
      0 * (x / 2), 1 * (x / 2), 0 * (x / 2), 0 * (x / 2);
      0 * (x + 1), 0 * (x + 1), 1 * (x + 1), 0 * (x + 1);
      0 * (x ^ 2), 0 * (x ^ 2), 0 * (x ^ 2), 1 * (x ^ 2)] =
      (det% !![1 * x, 0 * x, 0 * x, 0 * x;
        0 * (x / 2), 1 * (x / 2), 0 * (x / 2), 0 * (x / 2);
        0 * (x + 1), 0 * (x + 1), 1 * (x + 1), 0 * (x + 1);
        0 * (x ^ 2), 0 * (x ^ 2), 0 * (x ^ 2), 1 * (x ^ 2)]).value :=
  (det% !![1 * x, 0 * x, 0 * x, 0 * x;
    0 * (x / 2), 1 * (x / 2), 0 * (x / 2), 0 * (x / 2);
    0 * (x + 1), 0 * (x + 1), 1 * (x + 1), 0 * (x + 1);
    0 * (x ^ 2), 0 * (x ^ 2), 0 * (x ^ 2), 1 * (x ^ 2)]).proof

-- Swaps transport to positive characteristic without an injectivity premise.
theorem swapped (x : ZMod 3) :
    Matrix.det !![0 * x, 1 * x, 0 * x, 0 * x;
      1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = (-1) * x * x * x * x := by det

theorem singular {R : Type u} [CommRing R] (x : R) :
    Matrix.det !![1 * x, 0 * x, 0 * x, 0 * x;
      1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = 0 * x * x * x * x := by det

-- A target requiring expansion takes the ordinary polynomial route.
example (x : Int) :
    Matrix.det !![1 * (x + 1), 0 * (x + 1), 0 * (x + 1), 0 * (x + 1);
      0 * x, 1 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = x ^ 4 + x ^ 3 := by det

-- A wrong coefficient in an otherwise factored target cannot be certified.
example (x : Int) (h :
    Matrix.det !![1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 1 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = 2 * x * x * x * x) :
    Matrix.det !![1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 1 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = 2 * x * x * x * x := by
  fail_if_success det
  exact h

theorem simplified (x : Int) :
    Matrix.det !![1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 1 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = 1 * x * x * x * x := by
  simp only [Hex.normPolyDet]

-- Pin the shortcut: valid proofs through a polynomial fallback do not suffice.
run_meta do
  for root in [``generic, ``term, ``swapped, ``singular, ``simplified] do
    let mut pending := [root]
    let mut found := false
    while let name :: rest := pending do
      pending := rest
      let some value := (← Lean.getConstInfo name).value? (allowOpaque := true)
        | throwError "missing row-factor proof"
      for used in value.getUsedConstants do
        if used == ``HexPolyDetMathlib.RowFactor.det then found := true
        if root.isPrefixOf used then pending := used :: pending
    unless found do throwError "{root} did not use the row-factor certificate"

/-- info: 'RowFactorTests.generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generic

end RowFactorTests

namespace StructuralTests

theorem diagonal {R : Type u} [CommRing R] (a b : R) :
    Matrix.det !![a, 0; 0, b] = a*b := by det

theorem upper {R : Type u} [CommRing R] (a b c d e f : R) :
    Matrix.det !![a, b, c; 0, d, e; 0, 0, f] = a*d*f := by det

theorem lower {R : Type u} [CommRing R] (a b c d e f : R) :
    a*d*f = Matrix.det !![a, 0, 0; b, d, 0; c, e, f] := by det

theorem zeroRow (a b c d e f : Int) :
    Matrix.det !![a, b, c; 0, 0, 0; d, e, f] = 0 := by det

theorem rational (a b c : Rat) :
    Matrix.det !![(-2)*a/2, 3*a/2, (-2)*a/2;
      (-3)*b/3, 1*b/3, 3*b/3;
      (-1)*c/4, (-3)*c/4, 1*c/4] = (-40)*a*b*c/24 := by det

theorem rationalChanged (a b c : Rat) :
    Matrix.det !![a/2, 2*a/2, 3*a/2;
      4*b/3, 0, 6*b/3;
      7*c/5, 8*c/5, 10*c/5] = 52*a*b*c/30 := by det

theorem rationalZero (a b : Rat) :
    Matrix.det !![a/0, 2*a/0; b/3, 4*b/3] = 0 := by det

theorem sparse {R : Type u} [CommRing R] (a b c d e : R) :
    Matrix.det !![a, 1, 1, 1, 0; 1, b, 1, 1, 0;
      1, 1, c, 1, 0; 1, 1, 1, d, 0; 0, 0, 0, 0, e] =
      (a*(b*(c*d-1) - (d-1) + (1-c)) -
       (c*d-1 - (d-1) + (1-c)) +
       (d-1 - b*(d-1) + (1-1)) -
       (1-c - b*(1-c) + (1-1)))*e := by det

-- A column cofactor in an odd position exercises transposition and its sign.
theorem sparseColumn (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a b c d e : Int) :
    Matrix.det !![x0, 0, x1, x2, x3; x4, 0, x5, x6, x7;
      x8, 0, x9, x10, x11; x12, 0, x13, x14, x15;
      a, e, b, c, d] = -e * (x0*(x5*(x10*x15-x11*x14) - x6*(x9*x15-x11*x13) + x7*(x9*x14-x10*x13)) - x1*(x4*(x10*x15-x11*x14) - x6*(x8*x15-x11*x12) + x7*(x8*x14-x10*x12)) + x2*(x4*(x9*x15-x11*x13) - x5*(x8*x15-x11*x12) + x7*(x8*x13-x9*x12)) - x3*(x4*(x9*x14-x10*x13) - x5*(x8*x14-x10*x12) + x6*(x8*x13-x9*x12))) := by det

-- Both the term form and simproc share structural dispatch.
theorem term (a b : Int) :
    (det% !![a, 0; 0, b]).value = a*b := by rfl

theorem simplified (a b : Rat) :
    Matrix.det !![a, 0; 0, b] = a*b := by simp only [Hex.normPolyDet]

theorem rationalReverse (a b : Rat) :
    a*b/6 = Matrix.det !![a/2, 3*a/2; b/3, 4*b/3] := by det

-- Two nonzero cofactors and two levels of reindexing, at the default heartbeat limit.
theorem sparseDeep (a b c d : Int) :
    5*(a*d-b*c) = Matrix.det !![2,1,1,1,0,0; 1,2,1,1,0,0;
      1,1,2,1,0,0; 1,1,1,2,0,0; 0,0,0,0,a,b; 0,0,0,0,c,d] := by det

theorem sparseTerm (a b c d : Int) :
    Matrix.det !![2,1,1,1,0,0; 1,2,1,1,0,0;
      1,1,2,1,0,0; 1,1,1,2,0,0; 0,0,0,0,a,b; 0,0,0,0,c,d] =
    (det% !![2,1,1,1,0,0; 1,2,1,1,0,0;
      1,1,2,1,0,0; 1,1,1,2,0,0; 0,0,0,0,a,b; 0,0,0,0,c,d]).value :=
  (det% !![2,1,1,1,0,0; 1,2,1,1,0,0;
      1,1,2,1,0,0; 1,1,1,2,0,0; 0,0,0,0,a,b; 0,0,0,0,c,d]).proof

theorem sparseSimp (a b c d : Int) :
    Matrix.det !![2,1,1,1,0,0; 1,2,1,1,0,0;
      1,1,2,1,0,0; 1,1,1,2,0,0; 0,0,0,0,a,b; 0,0,0,0,c,d] = 5*(a*d-b*c) := by
  simp only [Hex.normPolyDet]
  ring

theorem residueFallback (a b : ZMod 3) :
    Matrix.det !![a, 0; 0, b] = a*b + 3*a*b := by det

run_meta do
  for (root, route) in [( ``diagonal, ``HexPolyDetMathlib.Structural.triangular),
      (``upper, ``HexPolyDetMathlib.Structural.triangular),
      (``lower, ``HexPolyDetMathlib.Structural.triangular),
      (``zeroRow, ``HexPolyDetMathlib.Structural.zeroRow),
      (``rational, ``HexPolyDetMathlib.RatFactor.det),
      (``rationalChanged, ``HexPolyDetMathlib.RatFactor.det),
      (``sparse, ``HexPolyDetMathlib.Structural.cofactor),
      (``sparseColumn, ``HexPolyDetMathlib.Structural.cofactor),
      (``sparseDeep, ``HexPolyDetMathlib.Structural.cofactor),
      (``sparseTerm, ``HexPolyDetMathlib.Structural.cofactor),
      (``sparseSimp, ``HexPolyDetMathlib.Structural.cofactor),
      (``rationalReverse, ``HexPolyDetMathlib.RatFactor.det),
      (``residueFallback, ``HexMatrixMathlib.DetPoly.Residue.target_det)] do
    let mut pending := [root]
    let mut found := false
    while let name :: rest := pending do
      pending := rest
      let some value := (← Lean.getConstInfo name).value? (allowOpaque := true)
        | throwError "missing structural proof"
      for used in value.getUsedConstants do
        if used == route then found := true
        if root.isPrefixOf used then pending := used :: pending
    unless found do throwError "{root} did not use {route}"

/-- info: 'StructuralTests.rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational
/-- info: 'StructuralTests.sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sparse
end StructuralTests

namespace StructuralBudgetTests
open Lean Meta HexMatrixMathlib.Literal

-- Two nonzero cofactors each terminate in a 4×4 formula: exactly 48 leaves.
run_meta do
  let zs := (List.range 5).toArray.map fun i =>
    (List.range 5).toArray.map fun j => i == 4 && j > 1
  unless (HexPolyDetMathlib.Structural.plan? zs false 48).isSome do
    throwError "sparse preflight rejected its exact leaf budget"
  unless (HexPolyDetMathlib.Structural.plan? zs false 47).isNone do
    throwError "sparse preflight exceeded its leaf budget"
  let dense := Array.replicate 8 (Array.replicate 8 false)
  unless (HexPolyDetMathlib.Structural.plan? dense false 64).isNone do
    throwError "dense matrix entered sparse expansion"

-- A rejected rational shortcut must not assign the user's target metavariable.
example (a b : Rat) : True := by
  let A : Matrix (Fin 2) (Fin 2) Rat := !![a/2, 3*a/2; b/3, 4*b/3]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing matrix"
    let some lit ← literal? a (allowOpen := true) | throwError "missing literal"
    let rhs ← mkFreshExprMVar (mkConst ``Rat)
    if (← HexPolyDetMathlib.RatFactor.compute? a lit (some rhs)).isSome then
      throwError "rational shortcut accepted a target metavariable"
    if ← rhs.mvarId!.isAssigned then throwError "rational shortcut assigned target"
  trivial

example (x : Rat) : True := by
  letI : HMul Rat Rat Rat := ⟨fun a b => a + b⟩
  let A : Matrix (Fin 2) (Fin 2) Rat := !![(1*x)/2, (2*x)/2; (3*x)/2, (4*x)/2]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing matrix"
    let some lit ← literal? a (allowOpen := true) | throwError "missing literal"
    if (← HexPolyDetMathlib.RatFactor.compute? a lit none).isSome then
      throwError "rational shortcut accepted non-ring multiplication"
  trivial

example (a b : Int) (h : Matrix.det !![a, 0; 0, b] = a*b+1) :
    Matrix.det !![a, 0; 0, b] = a*b+1 := by
  fail_if_success det
  exact h

example (a b : Rat) (h : Matrix.det !![a/2, 3*a/2; b/3, 4*b/3] = a*b/3) :
    Matrix.det !![a/2, 3*a/2; b/3, 4*b/3] = a*b/3 := by
  fail_if_success det
  exact h

example (a b : ZMod 3) : Matrix.det !![a, 0; 0, b] = a*b := by det

example (f : Rat → Rat) (a b : Rat) :
    Matrix.det !![f a/2, 3*f a/2; f b/3, 4*f b/3] = f a*f b/6 := by det

example (a b : Rat) :
    Matrix.det !![a/2, 3*a/2; b/3, 4*b/3] =
      (det% !![a/2, 3*a/2; b/3, 4*b/3]).value :=
  (det% !![a/2, 3*a/2; b/3, 4*b/3]).proof

example (a b : Rat) :
    Matrix.det !![a/2, 3*a/2; b/3, 4*b/3] = (1/6)*a*b := by
  simp only [Hex.normPolyDet]
-- Structural recognition must use the ring's operations, not local overrides.
example (a b : Int) : True := by
  letI : HMul Int Int Int := ⟨fun a b => a + b⟩
  let A : Matrix (Fin 2) (Fin 2) Int := !![a, 0; 0, b]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing matrix"
    let some lit ← literal? a (allowOpen := true) | throwError "missing literal"
    if (← HexPolyDetMathlib.Structural.direct? a lit).isSome then
      throwError "triangular shortcut accepted non-ring multiplication"
  trivial

-- A mixed-type multiplication must decline without constructing an ill-typed factor list.
example (x : Nat) : True := by
  letI : HMul Rat Nat Rat := ⟨fun a b => a + b⟩
  let A : Matrix (Fin 2) (Fin 2) Rat := !![((1 : Rat)*x)/2, ((2 : Rat)*x)/2; ((3 : Rat)*x)/2, ((4 : Rat)*x)/2]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing matrix"
    let some lit ← literal? a (allowOpen := true) | throwError "missing literal"
    if (← HexPolyDetMathlib.RatFactor.compute? a lit none).isSome then
      throwError "accepted a factor of the wrong type"
  trivial

-- The mixed division does not provide an HMul Rat Nat Rat instance.
example (x : Nat) : True := by
  letI : HDiv Nat Rat Rat := ⟨fun x q => (x : Rat) + q⟩
  let A : Matrix (Fin 2) (Fin 2) Rat := !![x/(2:Rat), x/(3:Rat); x/(4:Rat), x/(5:Rat)]
  run_tac Lean.Elab.Tactic.withMainContext do
    let a ← getFVarFromUserName `A
    let some a := (← a.fvarId!.getDecl).value? | throwError "missing matrix"
    let some lit ← literal? a (allowOpen := true) | throwError "missing literal"
    if (← HexPolyDetMathlib.RatFactor.compute? a lit none).isSome then
      throwError "accepted mixed-type division"
  trivial

-- Finalization and assembly must both decline at a deliberately small node budget.
example (a b : Int) : True := by
  let A : Matrix (Fin 2) (Fin 2) Int := !![a,0;0,b]
  let B : Matrix (Fin 5) (Fin 5) Int := !![a,1,1,1,0;1,a,1,1,0;
    1,1,a,1,0;1,1,1,a,0;0,0,0,0,b]
  run_tac Lean.Elab.Tactic.withMainContext do
    let config : Hex.Reflect.Config := {budget := {Hex.Reflect.Budget.default with proofNodes := 1}}
    for (name, direct) in [(`A, true), (`B, false)] do
      let matrix ← getFVarFromUserName name
      let some matrix := (← matrix.fvarId!.getDecl).value? | throwError "missing matrix"
      let some lit ← literal? matrix (allowOpen := true) | throwError "missing literal"
      let result ← if direct then HexPolyDetMathlib.Structural.direct? matrix lit config
        else HexPolyDetMathlib.Structural.sparse? matrix lit config
      if result.isSome then throwError "ignored structural proof-node budget"
  trivial

end StructuralBudgetTests

namespace ComponentTests
open Lean Meta Elab Tactic HexMatrixMathlib.DetPoly.Frontend

-- Both component lemmas must close over a retained let and universe parameter.
theorem closedComponents {α : Type u} (x : α) : x = x ∧ x = x := by
  let y := x
  run_tac withMainContext do
    let y ← getFVarFromUserName `y
    let h ← mkEqRefl y
    let proof ← mkAppM ``And.intro #[h, h]
    let target ← getMainTarget
    let .success (checked, count) usage ← Hex.Reflect.run <| Hex.Reflect.withOutcome <|
        checkedBudgeted target proof | throwError "component check failed"
    unless count == usage.proofNodes do throwError "component accounting omitted nodes"
    -- A budget one node short must decline after checking the components,
    -- rather than resetting the budget for the final composition.
    let config : Hex.Reflect.Config :=
      { budget := { Hex.Reflect.Budget.default with proofNodes := count - 1 } }
    let .declined (.budgetExhausted exhausted) partialUsage ← Hex.Reflect.run
        (Hex.Reflect.withOutcome <| checkedBudgeted target proof) config
      | throwError "component checks escaped the shared budget"
    unless exhausted.dimension == .proofNodes && partialUsage.proofNodes > 0 do
      throwError "expected exhaustion after component admission"
    let (_, closed, _) ← closeProof (← inferType h) h
    unless partialUsage.proofNodes == Hex.Reflect.proofNodeCount #[closed] count do
      throwError "charged the identical component payload twice"
    let config := { config with budget.proofNodes := count }
    let .success (_, exactCount) _ ← Hex.Reflect.run
        (Hex.Reflect.withOutcome <| checkedBudgeted target proof) config
      | throwError "exact component budget was rejected"
    unless exactCount == count do throwError "component count changed"
    closeMainGoal `det checked

/-- info: 'ComponentTests.closedComponents' does not depend on any axioms -/
#guard_msgs in
#print axioms closedComponents

-- The retained let occurs only in an assigned metavariable's value.
theorem assignedProof {α : Type u} (x : α) : x = x := by
  let y := x
  run_tac withMainContext do
    let h ← mkEqRefl (← getFVarFromUserName `y)
    let proof ← mkFreshExprMVar (← inferType h)
    proof.mvarId!.assign h
    closeMainGoal `det (← checked (← getMainTarget) proof)

/-- info: 'ComponentTests.assignedProof' does not depend on any axioms -/
#guard_msgs in
#print axioms assignedProof

end ComponentTests

-- Exceeding Hex's dimension budget cannot invoke Mathlib, even when imported.
example (x : Int) (h : ∀ A : Matrix (Fin 17) (Fin 17) Int, A.det = x ^ 17) :
    Matrix.det !![
    x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, x] = x ^ 17 := by
  fail_if_success det
  fail_if_success simp only [Hex.normPolyDet]
  exact h _
