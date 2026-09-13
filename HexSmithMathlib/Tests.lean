/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexSmithMathlib.Tactic

/-! Kernel certificate and frontend conformance for integer Smith quotients. -/

open HexSmithMathlib HexMatrixMathlib
open scoped DirectSum

noncomputable def smithDiagonal : SmithQuotient !![2, 0; 0, 6] 2 ![2, 6] := by smith

theorem smithDiagonalExists : Nonempty (SmithQuotient !![2, 0; 0, 6] 2 ![2, 6]) := by smith

noncomputable def smithWide : SmithQuotient !![-2, -4] 1 ![2] := by smith

noncomputable def smithEmpty : SmithQuotient (!![,,,] : Matrix (Fin 0) (Fin 3) ℤ) 0 ![] := by smith

noncomputable def smithNoColumns : SmithQuotient (!![;;;] : Matrix (Fin 3) (Fin 0) ℤ) 0 ![] := by smith

noncomputable def smithTall : SmithQuotient !![2; -4; 6] 1 ![2] := by smith

noncomputable def smithZero : SmithQuotient !![0, 0; 0, 0] 0 ![] := by smith

example : Nonempty (SmithQuotient (Matrix.of ![![2, 0], ![0, 6]]) 2 ![2, 6]) := by smith

example : Nonempty (SmithQuotient
    (fun i j : Fin 2 => if i = j then (2 : ℤ) else 0) 2 ![2, 2]) := by smith

example : Nonempty (SmithQuotient
    (Matrix.ofArray (m := 2) (n := 2) #[(2 : ℤ), 0, 0, 6] rfl) 2 ![2, 6]) := by smith

def smithMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 6]
def smithMatrixAlias := smithMatrix

example : Nonempty (SmithQuotient smithMatrixAlias 2 (fun i => if i = 0 then 2 else 6)) := by smith

example : (smith% !![2, 0; 0, 6]).rank = 2 := rfl

example : (smith% !![1, 0]).factors 0 = 1 := rfl

example : (smith% !![2, 0; 0, 6]).rank ≤ min 2 2 :=
  (smith% !![2, 0; 0, 6]).rank_le

example (i : Fin 2) : 0 < (smith% !![2, 0; 0, 6]).factors i :=
  (smith% !![2, 0; 0, 6]).positive i

example : (smith% !![2, 0; 0, 6]).factors 0 ∣ (smith% !![2, 0; 0, 6]).factors 1 :=
  (smith% !![2, 0; 0, 6]).chain 0 1 rfl

noncomputable def smithTermEquiv : SmithQuotient !![2, 0; 0, 6] 2 ![2, 6] :=
  (smith% !![2, 0; 0, 6]).equiv

def smithCertificate : Hex.Matrix.SmithWitness where
  rank := 2
  diag := [2, 6]
  left := [[1, 0], [0, 1]]
  leftInv := [[1, 0], [0, 1]]
  right := [[1, 0], [0, 1]]
  rightInv := [[1, 0], [0, 1]]
  intermediate := [[2, 0], [0, 6]]

theorem smithCertificateChecked :
    Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]] smithCertificate = true := by decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with leftInv := [[2, 0], [0, 1]] } = false := by decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with diag := [2, 5] } = false := by decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with right := [[1, 0]] } = false := by decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 3]]
    { smithCertificate with diag := [2, 3], intermediate := [[2, 0], [0, 3]] } = false := by
  decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with
      left := [[-1, 0], [0, -1]]
      leftInv := [[-1, 0], [0, -1]]
      right := [[-1, 0], [0, -1]]
      rightInv := [[-1, 0], [0, -1]]
      intermediate := [[-2, 0], [0, -6]] } = true := by decide +kernel

-- Keep dimensions, invertibility and the chain valid while corrupting each
-- product connecting the presentation to its diagonal.
example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with
      left := [[1, 1], [0, 1]]
      leftInv := [[1, -1], [0, 1]] } = false := by decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with
      right := [[0, 1], [1, 0]]
      rightInv := [[0, 1], [1, 0]] } = false := by decide +kernel

example : Hex.Matrix.checkSmithList 2 2 [[2, 0], [0, 6]]
    { smithCertificate with diag := [2, 8] } = false := by decide +kernel

/-- info: '_private.HexSmithMathlib.Tests.0.smithDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smithDiagonal
/-- info: '_private.HexSmithMathlib.Tests.0.smithDiagonalExists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smithDiagonalExists
/-- info: '_private.HexSmithMathlib.Tests.0.smithCertificateChecked' depends on axioms: [propext] -/
#guard_msgs in
#print axioms smithCertificateChecked
/-- info: '_private.HexSmithMathlib.Tests.0.smithTermEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms smithTermEquiv

/-- error: smith: the target factors do not match: rank 2, factors [2, 6] -/
#guard_msgs in
example : Nonempty (SmithQuotient !![2, 0; 0, 6] 2 ![-2, -6]) := by smith

/--
error: smith: declined: the factor function must be a closed vector literal
  d
-/
#guard_msgs in
example (d : Fin 2 → ℤ) : Nonempty (SmithQuotient !![2, 0; 0, 6] 2 d) := by smith

/--
error: smith: declined: the matrix must be a closed literal within the unfolding budget of 8
  A
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℤ) : Nonempty (SmithQuotient A 2 ![2, 6]) := by smith

/-- error: smith: expected an integer row-presentation quotient equivalence or its Nonempty wrapper -/
#guard_msgs in
example : (2 : ℕ) = 3 := by smith

open Lean Elab Tactic

run_cmd do
  let handlers := (tacticElabAttribute.getEntries (← getEnv) ``HexSmithMathlib.Tactic.smithTac).map (·.declName)
  unless handlers == [``HexSmithMathlib.Tactic.evalSmith, ``HexSmithMathlib.Tactic.smithFallback] do
    throwError "unexpected shipped handler order: {handlers}"

section Delegation

@[no_fallback]
private meta def extensionStub : Tactic := fun _ => do
  logInfo "structural extension"
  evalTactic (← `(tactic| assumption))

attribute [local tactic HexSmithMathlib.Tactic.smithTac] extensionStub
attribute [local tactic HexSmithMathlib.Tactic.smithTac] HexSmithMathlib.Tactic.evalSmith

/-- info: structural extension -/
#guard_msgs in
example (h : True) : True := by smith

/-- error: smith: the target factors do not match: rank 1, factors [2] -/
#guard_msgs in
example (h : Nonempty (SmithQuotient !![2] 1 ![3])) : Nonempty (SmithQuotient !![2] 1 ![3]) := by smith

end Delegation

section TermDelegation

private meta def termStub : Term.TermElab := fun _ _ => do
  logInfo "structural term extension"
  return Lean.mkNatLit 2

attribute [local term_elab HexSmithMathlib.Tactic.smithTerm] termStub
attribute [local term_elab HexSmithMathlib.Tactic.smithTerm] HexSmithMathlib.Tactic.elabSmithTerm

/-- info: structural term extension -/
#guard_msgs in
example : (smith% (2 : ℕ)) = 2 := rfl

end TermDelegation
