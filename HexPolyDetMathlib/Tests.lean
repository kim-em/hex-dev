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

-- Swaps and characteristic reduction belong to the numeric transport too.
example (x : ZMod 3) :
    Matrix.det !![0 * x, 1 * x, 0 * x, 0 * x;
      1 * x, 0 * x, 0 * x, 0 * x;
      0 * x, 0 * x, 1 * x, 0 * x;
      0 * x, 0 * x, 0 * x, 1 * x] = (-1) * x * x * x * x := by det

example {R : Type u} [CommRing R] (x : R) :
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

-- Pin the shortcut: valid proofs through a polynomial fallback do not suffice.
run_meta do
  for root in [``generic, ``term] do
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
