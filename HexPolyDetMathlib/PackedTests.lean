/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib
import Mathlib.Algebra.Field.ZMod

set_option hex.det.checker 2
set_option trace.HexMatrix.certificate true

theorem packedInteger (x y : Int) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 - 1) * (y ^ 2 - 1) := by det

set_option hex.det.checker 0 in
theorem automaticPacked (x y : Int) :
    let a := x ^ 2 + 2 * x + 3 * y + 1
    let b := 2 * y ^ 2 + 3 * y + x + 2
    let c := 3 * x ^ 2 + x + 2 * y + 3 * y ^ 2
    let d := y ^ 2 + 2 * y + 3 * x + x ^ 2
    Matrix.det !![-3 * a, -2 * a, -3 * a, 3 * a;
      -b, b, -3 * b, -b; 3 * c, 3 * c, -2 * c, -c;
      3 * d, 2 * d, -d, -d] = -26 * a * b * c * d := by
  dsimp only
  det

theorem packedResidue (x y : ZMod 3) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 - 1) * (y ^ 2 - 1) := by det

example [Fact (Nat.Prime 2147483647)] (x y : ZMod 2147483647) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 - 1) * (y ^ 2 - 1) := by det

theorem packedTerm (x y : Int) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).value :=
  (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).proof

example (x y : Int) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (x ^ 2 - 1) * (y ^ 2 - 1) := by
  simp only [Hex.normPolyDet]
  ring

theorem packedRational (x y : Rat) :
    Matrix.det !![x / 2, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 / 2 - 1) * (y ^ 2 - 1) := by det

set_option hex.det.checker 3 in
example (x y : Int) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (x ^ 2 - 1) * (y ^ 2 - 1) := by det

set_option hex.det.quotients false in
example (x y : ZMod 3) : Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
    (x ^ 2 - 1) * (y ^ 2 - 1) := by det

/-- info: 'packedInteger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedInteger
/-- info: 'packedResidue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedResidue

/-- info: 'HexMatrixMathlib.DetPoly.Polynomial.checkDetPolyPacked_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexMatrixMathlib.DetPoly.Polynomial.checkDetPolyPacked_sound
/-- info: 'HexMatrixMathlib.DetPoly.Residue.checkDetPolyPackedMod_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexMatrixMathlib.DetPoly.Residue.checkDetPolyPackedMod_sound

set_option maxHeartbeats 0 in
example (x : Fin 17 → Int) : ∃ d : Int, Matrix.det !![x 0, x 1, x 2, x 3, 0; x 4, x 5, x 6, x 7, 0; x 8, x 9, x 10, x 11, 0; x 12, x 13, x 14, x 15, 0; 0, 0, 0, 0, x 16] = d := by
  exact ⟨_, (det% !![x 0, x 1, x 2, x 3, 0; x 4, x 5, x 6, x 7, 0; x 8, x 9, x 10, x 11, 0; x 12, x 13, x 14, x 15, 0; 0, 0, 0, 0, x 16]).proof⟩

theorem packedSingular (x y : Int) :
    Matrix.det !![x, 1, y, 0; x, 1, y, 0; 0, y, 1, x; 1, 0, x, y] = 0 := by det

theorem packedSingularMod (x y : ZMod 3) :
    Matrix.det !![x, 1, y, 0; x, 1, y, 0; 0, y, 1, x; 1, 0, x, y] = 0 := by det

/-- info: 'packedRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedRational
/-- info: 'packedTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedTerm
/-- info: 'packedSingular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedSingular
/-- info: 'packedSingularMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms packedSingularMod

universe u

-- Tree transport supports carriers in arbitrary universes, with no domain premise.
set_option hex.det.checker 2 in
theorem packedUniverse {R : Type u} [CommRing R] (x y : R) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x * x - 1) * (y * y - 1) := by det

-- A target may fail structural preflight although all witness products fit.
-- The canonical-list route still certifies the cancellation in that target.
set_option hex.det.checker 2 in
example (x y z w : Int) : Matrix.det !![x, 0, 0, 0; 0, y, 0, 0; 0, 0, z, 0; 0, 0, 0, w] =
    x * y * z * w + (x ^ 64 * y ^ 64 * z ^ 64 * w ^ 64 - x ^ 64 * y ^ 64 * z ^ 64 * w ^ 64) := by
  det

/-- info: 'HexMatrixMathlib.DetPoly.Tree.checkDetPolyPackedTree_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexMatrixMathlib.DetPoly.Tree.checkDetPolyPackedTree_sound
/-- info: 'packedUniverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms packedUniverse

-- Generated values are identified structurally, without a target certificate.
run_meta do
  let mut pending := [``packedTerm]
  while let name :: rest := pending do
    pending := rest
    let some value := (← Lean.getConstInfo name).value? (allowOpaque := true)
      | throwError "missing generated term proof"
    for used in value.getUsedConstants do
      if used == ``Hex.Kronecker.Kernel.treeTermsEq_sound ||
          used == ``HexReflectMathlib.Kernel.eval_checked then
        throwError "generated term redundantly checks its reconstructed value"
      if (``packedTerm).isPrefixOf used then pending := used :: pending

example (x y : Rat) :
    (det% !![x / 2, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).value =
      (x ^ 2 / 2 - 1) * (y ^ 2 - 1) := by ring

-- Generated values also authenticate their instances over abstract carriers.
set_option hex.det.checker 2 in
theorem packedTermUniverse {R : Type u} [CommRing R] (x y : R) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).value :=
  (det% !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y]).proof

/-- info: 'packedTermUniverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms packedTermUniverse

-- Let-bound data must count towards admission even when the open proof is tiny.
run_meta do
  let outcome ← Hex.Reflect.run (Hex.Reflect.withOutcome do
    let mut payload := Lean.mkNatLit 0
    for _ in [:100] do payload := Lean.mkApp (Lean.mkConst ``Nat.succ) payload
    Lean.Meta.withLetDecl `retained (Lean.mkConst ``Nat) payload fun x => do
      HexMatrixMathlib.DetPoly.Frontend.checkedBudgeted (← Lean.Meta.mkEq x x)
        (← Lean.Meta.mkEqRefl x)) { budget := { Hex.Reflect.Budget.default with proofNodes := 100 } }
  match outcome with
  | .declined (.budgetExhausted e) _ =>
    unless e.dimension == .proofNodes do throwError "wrong budget dimension"
  | _ => throwError "retained proof payload escaped its node budget"

-- Repeated shared syntax must neither inflate the count nor defeat its cap.
run_meta do
  let mut e := Lean.mkRawNatLit 0
  for _ in [:64] do e := Lean.mkApp e e
  unless Hex.Reflect.proofNodeCount #[e] 32 == 32 do
    throwError "proof-node counting did not stop at its cap"
  unless Hex.Reflect.proofNodeCount #[e] 1000 == 65 do
    throwError "shared syntax count {Hex.Reflect.proofNodeCount #[e] 1000}"

-- Pin the abstract term form to the tree route, not merely to a valid fallback.
run_meta do
  let mut pending := [``packedTermUniverse]
  let mut found := false
  while let name :: rest := pending do
    pending := rest
    let some value := (← Lean.getConstInfo name).value? (allowOpaque := true)
      | throwError "missing generated abstract-carrier proof"
    for used in value.getUsedConstants do
      if used == ``HexMatrixMathlib.DetPoly.Tree.result_det then found := true
      if (``packedTermUniverse).isPrefixOf used then pending := used :: pending
  unless found do throwError "abstract term form did not use the tree certificate"
