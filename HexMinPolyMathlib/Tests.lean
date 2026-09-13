/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexMinPolyMathlib.Tactic

open HexMinPolyMathlib Polynomial

theorem minPolyDiagonal : minpoly ℚ (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) =
    X ^ 2 - 5 * X + 6 := by min_poly

theorem minPolyReversed : (X - 2) * (X - 3) =
    minpoly ℚ (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℚ) := by min_poly

theorem minPolyRational : minpoly ℚ (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℚ) =
    X - C (1 / 2) := by min_poly

theorem minPolyNilpotent : minpoly ℚ (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) =
    X ^ 2 := by min_poly

theorem minPolyEmpty : minpoly ℚ (!![] : Matrix (Fin 0) (Fin 0) ℚ) = 1 := by min_poly

example : minpoly ℚ (Matrix.of ![![2, 0], ![0, 3]] : Matrix (Fin 2) (Fin 2) ℚ) =
    (X - 2) * (X - 3) := by min_poly

example : minpoly ℚ (B := Matrix (Fin 2) (Fin 2) ℚ)
    (fun i j => if i = j then (1 / 2 : ℚ) else 0) =
    X - C (1 / 2) := by min_poly

example : minpoly ℚ (Matrix.ofArray (m := 2) (n := 2) #[(0 : ℚ), 1, 0, 0] rfl) =
    X ^ 2 := by min_poly

def rationalMatrix : Matrix (Fin 2) (Fin 2) ℚ := !![1 / 2, 1 / 3; 0, 1 / 2]
def rationalMatrixAlias := rationalMatrix

example : minpoly ℚ rationalMatrixAlias = (X - C (1 / 2)) ^ 2 := by min_poly

noncomputable def minPolyResult : MinPolyResult !![1 / 2] := min_poly% !![1 / 2]

example : minpoly ℚ (!![1 / 2] : Matrix (Fin 1) (Fin 1) ℚ) = minPolyResult.value :=
  minPolyResult.proof

def minPolyCertificate : Hex.Matrix.MinPolyWitness where
  input := ⟨1, [[2]]⟩
  poly := ⟨1, [-2, 1]⟩
  order := [⟨⟨1, [-2, 1]⟩, 1, ⟨1, [[1]]⟩⟩]
  steps := [⟨⟨1, [1]⟩, ⟨1, [1]⟩, ⟨1, [-2, 1]⟩, ⟨1, [1]⟩, ⟨1, []⟩, ⟨1, [-2, 1]⟩⟩]

theorem minPolyCertificateChecked :
    Hex.Matrix.checkMinPolyList 1 [[2]] minPolyCertificate = true := by decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with order := [] } = false := by decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with input := ⟨0, [[2]]⟩ } = false := by decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with poly := ⟨1, [-3, 1]⟩ } = false := by decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with order := [⟨⟨1, [-2, 1]⟩, 1, ⟨1, [[2]]⟩⟩] } = false := by
  decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with poly := ⟨1, [-4, 2]⟩ } = false := by decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with poly := ⟨0, [-2, 1]⟩ } = false := by decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with order := [⟨⟨1, [4, -4, 1]⟩, 2, ⟨1, [[1, 0]]⟩⟩] } = false := by
  decide +kernel

example : Hex.Matrix.checkMinPolyList 1 [[2]]
    { minPolyCertificate with steps :=
      [⟨⟨1, [1]⟩, ⟨1, [1]⟩, ⟨1, [-2, 1]⟩, ⟨1, []⟩, ⟨1, []⟩, ⟨1, [-2, 1]⟩⟩] } = false := by
  decide +kernel

/-- info: '_private.HexMinPolyMathlib.Tests.0.minPolyDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minPolyDiagonal
/-- info: '_private.HexMinPolyMathlib.Tests.0.minPolyReversed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minPolyReversed
/-- info: '_private.HexMinPolyMathlib.Tests.0.minPolyRational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minPolyRational
/-- info: '_private.HexMinPolyMathlib.Tests.0.minPolyNilpotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minPolyNilpotent
/-- info: '_private.HexMinPolyMathlib.Tests.0.minPolyEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minPolyEmpty
/-- info: '_private.HexMinPolyMathlib.Tests.0.minPolyCertificateChecked' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms minPolyCertificateChecked

/-- error: min_poly: the stated polynomial is false; computed ascending coefficients [-2, 1] -/
#guard_msgs in
example : minpoly ℚ (!![2] : Matrix (Fin 1) (Fin 1) ℚ) = X - 3 := by min_poly

/-- error: min_poly: declined: dimension 17 exceeds the configured dimension budget of 16 -/
#guard_msgs in
example : minpoly ℚ (B := Matrix (Fin 17) (Fin 17) ℚ) (fun _ _ => 0) = X := by min_poly

/--
error: min_poly: declined: the matrix must be a closed literal within the unfolding budget of 8
  !![a]
-/
#guard_msgs in
example (a : ℚ) : minpoly ℚ (!![a] : Matrix (Fin 1) (Fin 1) ℚ) = X := by min_poly

/-- error: min_poly: expected minpoly ℚ A = p or p = minpoly ℚ A for a square rational literal -/
#guard_msgs in
example {F : Type} [Field F] (A : Matrix (Fin 1) (Fin 1) F) : minpoly F A = 0 := by min_poly

/-- error: min_poly: expected minpoly ℚ A = p or p = minpoly ℚ A for a square rational literal -/
#guard_msgs in
example : minpoly ℚ (fun i j : Fin 2 => if i = j then (1 / 2 : ℚ) else 0) = X := by min_poly

open Lean Elab Tactic

run_cmd do
  let handlers := (tacticElabAttribute.getEntries (← getEnv) ``HexMinPolyMathlib.Tactic.minPolyTac).map (·.declName)
  unless handlers == [``HexMinPolyMathlib.Tactic.evalMinPoly, ``HexMinPolyMathlib.Tactic.minpolyFallback] do
    throwError "unexpected shipped handler order: {handlers}"

section Delegation

@[no_fallback]
private meta def extensionStub : Tactic := fun _ => do
  logInfo "structural extension"
  evalTactic (← `(tactic| assumption))

attribute [local tactic HexMinPolyMathlib.Tactic.minPolyTac] extensionStub
attribute [local tactic HexMinPolyMathlib.Tactic.minPolyTac] HexMinPolyMathlib.Tactic.evalMinPoly

run_cmd do
  let handlers := (tacticElabAttribute.getEntries (← getEnv) ``HexMinPolyMathlib.Tactic.minPolyTac).map (·.declName)
  unless handlers == [``HexMinPolyMathlib.Tactic.evalMinPoly, ``extensionStub,
      ``HexMinPolyMathlib.Tactic.evalMinPoly, ``HexMinPolyMathlib.Tactic.minpolyFallback] do
    throwError "unexpected delegation handler order: {handlers}"

/-- info: structural extension -/
#guard_msgs in
example (h : True) : True := by min_poly

/-- error: min_poly: the stated polynomial is false; computed ascending coefficients [-2, 1] -/
#guard_msgs in
example (h : minpoly ℚ (!![2] : Matrix (Fin 1) (Fin 1) ℚ) = X - 3) : minpoly ℚ (!![2] : Matrix (Fin 1) (Fin 1) ℚ) = X - 3 := by min_poly

end Delegation

def repeatedOrders : Hex.Matrix.MinPolyWitness where
  input := ⟨1, [[2, 0, 0], [0, 2, 0], [0, 0, 3]]⟩
  poly := ⟨1, [6, -5, 1]⟩
  order := [⟨⟨1, [-2, 1]⟩, 1, ⟨1, [[1], [0], [0]]⟩⟩,
    ⟨⟨1, [-2, 1]⟩, 1, ⟨1, [[0], [1], [0]]⟩⟩,
    ⟨⟨1, [-3, 1]⟩, 1, ⟨1, [[0], [0], [1]]⟩⟩]
  steps := [⟨⟨1, [1]⟩, ⟨1, [1]⟩, ⟨1, [-2, 1]⟩, ⟨1, [1]⟩, ⟨1, []⟩, ⟨1, [-2, 1]⟩⟩,
    ⟨⟨1, [-2, 1]⟩, ⟨1, [1]⟩, ⟨1, [1]⟩, ⟨1, [1]⟩, ⟨1, []⟩, ⟨1, [-2, 1]⟩⟩,
    ⟨⟨1, [1]⟩, ⟨1, [-2, 1]⟩, ⟨1, [-3, 1]⟩, ⟨1, [1]⟩, ⟨1, [-1]⟩, ⟨1, [6, -5, 1]⟩⟩]

example : Hex.Matrix.checkMinPolyList 3 [[2, 0, 0], [0, 2, 0], [0, 0, 3]] repeatedOrders = true := by
  decide +kernel

example : Hex.Matrix.checkMinPolyList 3 [[2, 0, 0], [0, 2, 0], [0, 0, 3]]
    { repeatedOrders with order := repeatedOrders.order.drop 1 ++ repeatedOrders.order.take 1 } = false := by
  decide +kernel

section TermDelegation

private meta def termStub : Term.TermElab := fun _ _ => do
  logInfo "structural term extension"
  return Lean.mkNatLit 2

attribute [local term_elab HexMinPolyMathlib.Tactic.minPolyTerm] termStub
attribute [local term_elab HexMinPolyMathlib.Tactic.minPolyTerm] HexMinPolyMathlib.Tactic.elabMinPolyTerm

/-- info: structural term extension -/
#guard_msgs in
example : (min_poly% (2 : ℕ)) = 2 := rfl

end TermDelegation

section ExtensionErrors

@[no_fallback]
private meta def extensionDecline : Tactic := fun _ =>
  throwError "min_poly: test capability decline"

attribute [local tactic HexMinPolyMathlib.Tactic.minPolyTac] extensionDecline

/-- error: min_poly: test capability decline -/
#guard_msgs in
example : True := by min_poly

end ExtensionErrors

-- The LCM fold still sees the same polynomial sequence; only basis indices change.
example : Hex.Matrix.checkMinPolyList 3 [[2, 0, 0], [0, 2, 0], [0, 0, 3]]
    { repeatedOrders with order :=
      [repeatedOrders.order[1]!, repeatedOrders.order[0]!, repeatedOrders.order[2]!] } = false := by
  decide +kernel
