/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexCharPoly

namespace Hex.CharPolyElabTests

open Hex
open scoped Hex

def empty : Matrix Int 0 0 := Matrix.mk #v[]
def one : Matrix Int 1 1 := #m[7]
def dense : Matrix Int 2 2 := #m[1, 2; 3, 4]
def diagonal : Matrix Int 3 3 := #m[2, 0, 0; 0, -3, 0; 0, 0, 5]
def huge : Matrix Int 1 1 := #m[9223372036854775808]
def fromFn : Matrix Int 2 2 := Matrix.ofFn fun i j =>
  if i = j then (i.val : Int) + 1 else 0

#check char_poly #m[1, 2; 3, 4]

example : (char_poly empty).poly = #p[1] := rfl
example : Matrix.charPoly empty = #p[1] := by char_poly
example : Matrix.charPoly one = #p[-7, 1] := by char_poly
example : Matrix.charPoly dense = #p[-2, -5, 1] := by char_poly
example : #p[-2, -5, 1] = Matrix.charPoly dense := by char_poly
example : Matrix.charPoly diagonal = #p[30, -11, -4, 1] := by char_poly
example : Matrix.charPoly huge = #p[-9223372036854775808, 1] := by char_poly
example : Matrix.charPoly fromFn = #p[2, -3, 1] := by char_poly

example : True := by
  char_poly dense
  have : Matrix.charPoly dense = poly := charPoly_eq
  exact True.intro

#check_failure char_poly (#m[1] : Matrix Nat 1 1)
/-- info: char_poly declined: expected a square matrix, but got dimensions 1 × 2 -/
#guard_msgs in
#check_failure char_poly (#m[1, 2] : Matrix Int 1 2)

/-- info: char_poly: the supplied polynomial has coefficients [1], but the computed characteristic polynomial has coefficients [-2, -5, 1] -/
#guard_msgs (whitespace := lax) in
#check_failure (char_poly : Matrix.charPoly dense = #p[1])

end Hex.CharPolyElabTests

namespace Hex.Matrix.CharPolyKernel

private def smallSteps : List Step :=
  [{ column := [1, -1, -6], vectors := [], coefficients := [1, -5, -2], product := [1, -5, -2, 24] },
   { column := [1, -4], vectors := [], coefficients := [1, -4], product := [1, -4] }]

private def smallWitness : Witness := ⟨24, 12, smallSteps⟩

example : checkCharPolyList 2 [[1, 2], [3, 4]] smallWitness [1, -5, -2] = true := by
  decide +kernel

#guard !checkCharPolyList 2 [[1, 2], [3, 4]] { smallWitness with width := 11 } [1, -5, -2]
#guard !checkCharPolyList 2 [[1, 2], [3, 4]] { smallWitness with bound := 23 } [1, -5, -2]
#guard !checkCharPolyList 2 [[1, 2], [3]] smallWitness [1, -5, -2]
#guard !checkCharPolyList 2 [[1, 2], [3, 4]] smallWitness [1, -5, -3]
#guard !checkCharPolyList 2 [[1, 2], [3, 4]] { smallWitness with steps := smallSteps.tail } [1, -5, -2]
#guard !checkCharPolyList 2 [[1, 2], [3, 4]]
  { smallWitness with steps :=
    { column := [1, -1, -7], vectors := [], coefficients := [1, -5, -2], product := [1, -5, -2, 24] } :: smallSteps.tail }
  [1, -5, -2]

#guard !checkCharPolyList 2 [[1, 2], [3, 4]]
  { smallWitness with steps := smallSteps.modify 0 (fun s => { s with product := [1, -5, -2, 23] }) } [1, -5, -2]

example : Certified Hex.CharPolyElabTests.dense := char_poly Hex.CharPolyElabTests.dense

private def matrix3 : Hex.Matrix Int 3 3 := #m[1, 2, 3; 4, 5, 6; 7, 8, 9]
example : Hex.Matrix.charPoly matrix3 = #p[0, -18, -15, 1] := by char_poly

example : Hex.Matrix.charPoly (#m[29, 106, -16, 45; -66, -41, 6, -106;
    123, -23, -125, 96; 11, 88, 97, -45] : Hex.Matrix Int 4 4) =
    #p[112023617, 1451563, 15099, 182, 1] := by char_poly

private def witness3 := produce matrix3
#guard checkCharPolyList 3 (toRows matrix3) witness3 [1, -15, -18, 0]
#guard !checkCharPolyList 3 (toRows matrix3)
  { witness3 with steps := witness3.steps.modify 0 (fun s => { s with vectors := [[62, 94]] }) }
  [1, -15, -18, 0]

/-- info: 'Hex.Matrix.CharPolyKernel.charPoly_eq_of_checkList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms charPoly_eq_of_checkList
theorem frontendAudit : Hex.Matrix.charPoly Hex.CharPolyElabTests.dense = #p[-2, -5, 1] := by
  char_poly
/-- info: '_private.HexCharPoly.CharPolyElabTests.0.Hex.Matrix.CharPolyKernel.frontendAudit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frontendAudit

-- A malformed reflection proof must be reported as a certificate failure.
run_meta do
  let prop ← Lean.Meta.mkEq (Lean.toExpr (0 : Int)) (Lean.toExpr (1 : Int))
  let result ← try
    pure (Except.ok (← Hex.CharPolyTactic.kernelDecideProof prop))
  catch ex => pure (Except.error (← ex.toMessageData.toString))
  match result with
  | .ok _ => throwError "the kernel accepted a false certificate"
  | .error message =>
    unless message.startsWith "char_poly failure:" do
      throwError "incorrect certificate diagnostic: {message}"

end Hex.Matrix.CharPolyKernel
