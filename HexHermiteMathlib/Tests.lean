/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexHermiteMathlib.Tactic

open HexHermiteMathlib HexMatrixMathlib

theorem hermiteMember : (![4, 12] : Fin 2 → ℤ) ∈ Submodule.span ℤ (Set.range !![2, 0; 0, 6]) := by
  hermite

theorem hermiteNonmember : (![4, 13] : Fin 2 → ℤ) ∉ Submodule.span ℤ (Set.range !![2, 0; 0, 6]) := by
  hermite

example : Nonempty (HermiteBasis !![0, 0; 0, 0] 0) := by hermite

example : (![0, 0] : Fin 2 → ℤ) ∈ Submodule.span ℤ (Set.range !![0, 0; 0, 0]) := by
  hermite

example : (![1, 0] : Fin 2 → ℤ) ∉ Submodule.span ℤ (Set.range !![0, 0; 0, 0]) := by
  hermite

example : (![0, 0, 0] : Fin 3 → ℤ) ∈
    Submodule.span ℤ (Set.range (!![,,,] : Matrix (Fin 0) (Fin 3) ℤ)) := by hermite

example : (![0, 1, 0] : Fin 3 → ℤ) ∉
    Submodule.span ℤ (Set.range (!![,,,] : Matrix (Fin 0) (Fin 3) ℤ)) := by hermite

noncomputable def hermiteBasis : HermiteBasis !![2, 0; 0, 6] 2 := by hermite

theorem hermiteBasisExists : Nonempty (HermiteBasis !![2, 0; 0, 6] 2) := by hermite

noncomputable def hermiteEmpty :
    HermiteBasis (!![,,,] : Matrix (Fin 0) (Fin 3) ℤ) 0 := by hermite

noncomputable def hermiteNoColumns :
    HermiteBasis (!![;;;] : Matrix (Fin 3) (Fin 0) ℤ) 0 := by hermite

example : (![] : Fin 0 → ℤ) ∈
    Submodule.span ℤ (Set.range (!![;;;] : Matrix (Fin 3) (Fin 0) ℤ)) := by hermite

example : (hermite% !![2, 0; 0, 6]).rank = 2 := rfl

example : (hermite% !![2, 0; 0, 6]).form 0 0 = 2 := rfl

example : (![0, 4] : Fin 2 → ℤ) ∈ Submodule.span ℤ (Set.range !![0, -2; 0, 4; 0, 0]) := by
  hermite

example : (![1, 4] : Fin 2 → ℤ) ∉ Submodule.span ℤ (Set.range !![0, -2; 0, 4; 0, 0]) := by
  hermite

example : Nonempty (HermiteBasis !![0, -2; 0, 4; 0, 0] 1) := by hermite

example : Nonempty (HermiteBasis (Matrix.of ![![2, 0], ![0, 6]]) 2) := by hermite

example : Nonempty (HermiteBasis
    (fun i j : Fin 2 => if i = j then (2 : ℤ) else 0) 2) := by hermite

example : Nonempty (HermiteBasis
    (Matrix.ofArray (m := 2) (n := 2) #[(2 : ℤ), 0, 0, 6] rfl) 2) := by hermite

def hermiteMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 6]
def hermiteMatrixAlias := hermiteMatrix

example : (fun i : Fin 2 => if i = 0 then (4 : ℤ) else 12) ∈
    Submodule.span ℤ (Set.range hermiteMatrixAlias) := by hermite

example (i : Fin (hermite% !![2, 0; 0, 6]).rank) :
    ((hermite% !![2, 0; 0, 6]).basis i : Fin 2 → ℤ) =
      (hermite% !![2, 0; 0, 6]).form ⟨i.val, by have := i.isLt; change i.val < 2 at this; omega⟩ :=
  (hermite% !![2, 0; 0, 6]).basis_row i

def hermiteCertificate : Hex.Matrix.HermiteWitness where
  rank := 2
  pivots := [0, 1]
  form := [[2, 0], [0, 6]]
  transform := [[1, 0], [0, 1]]
  inverse := [[1, 0], [0, 1]]

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 6]] hermiteCertificate = true := by
  decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 6]]
    { hermiteCertificate with inverse := [[2, 0], [0, 1]] } = false := by decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 6]]
    { hermiteCertificate with pivots := [1, 0] } = false := by decide +kernel

example : Hex.Matrix.checkRemainder 2 [4, 13] hermiteCertificate ⟨[2, 2], [0, 1]⟩ = true := by
  decide +kernel

example : Hex.Matrix.checkRemainder 2 [4, 13] hermiteCertificate ⟨[2, 2], [0, 0]⟩ = false := by
  decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 6]]
    { hermiteCertificate with pivots := [0, 0] } = false := by decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 6]]
    { hermiteCertificate with pivots := [0, 2] } = false := by decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 6]]
    { hermiteCertificate with rank := 1, pivots := [0] } = false := by decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 6], [0, 6]]
    { hermiteCertificate with form := [[2, 6], [0, 6]] } = false := by decide +kernel

example : Hex.Matrix.checkRemainder 2 [4, 13] hermiteCertificate ⟨[2, 1], [0, 7]⟩ = false := by
  decide +kernel

example : Hex.Matrix.checkHermiteList 2 2 [[2, 0], [0, 0]]
    { rank := 1, pivots := [0], form := [[2, 0], [0, 0]],
      transform := [[1, 1], [0, 1]], inverse := [[1, -1], [0, 1]] } = true := by decide +kernel

/-- info: '_private.HexHermiteMathlib.Tests.0.hermiteMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hermiteMember
/-- info: '_private.HexHermiteMathlib.Tests.0.hermiteNonmember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hermiteNonmember
/-- info: '_private.HexHermiteMathlib.Tests.0.hermiteBasisExists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hermiteBasisExists

/-- error: hermite: the vector is not a member; nonzero residual [0, 1] -/
#guard_msgs in
example : (![4, 13] : Fin 2 → ℤ) ∈ Submodule.span ℤ (Set.range !![2, 0; 0, 6]) := by hermite

/-- error: hermite: the vector is a member; HNF coefficients [2, 2] -/
#guard_msgs in
example : (![4, 12] : Fin 2 → ℤ) ∉ Submodule.span ℤ (Set.range !![2, 0; 0, 6]) := by hermite

/-- error: hermite: the basis dimension does not match: rank 2 -/
#guard_msgs in
example : Nonempty (HermiteBasis !![2, 0; 0, 6] 1) := by hermite

/--
error: hermite: declined: the lattice vector must be a closed vector literal
  v
-/
#guard_msgs in
example (v : Fin 2 → ℤ) : v ∈ Submodule.span ℤ (Set.range !![2, 0; 0, 6]) := by hermite

/--
error: hermite: declined: the matrix must be a closed literal within the unfolding budget of 8
  A
-/
#guard_msgs in
example (A : Matrix (Fin 2) (Fin 2) ℤ) : Nonempty (HermiteBasis A 2) := by hermite

/-- error: hermite: expected integer row-lattice membership, nonmembership, or a row-lattice basis -/
#guard_msgs in
example : (2 : ℕ) = 3 := by hermite

/-- error: hermite: expected integer row-lattice membership, nonmembership, or a row-lattice basis -/
#guard_msgs in
example : (![2] : Fin 1 → ℤ) ∈
    (Submodule.span ℤ (Set.range !![2]) ⊓ ⊥) := by hermite

open Lean Elab Tactic

run_cmd do
  let handlers := (tacticElabAttribute.getEntries (← getEnv) ``HexHermiteMathlib.Tactic.hermiteTac).map (·.declName)
  unless handlers == [``HexHermiteMathlib.Tactic.evalHermite, ``HexHermiteMathlib.Tactic.hermiteFallback] do
    throwError "unexpected shipped handler order: {handlers}"

section Delegation

@[no_fallback]
private meta def extensionStub : Tactic := fun _ => do
  logInfo "structural extension"
  evalTactic (← `(tactic| assumption))

attribute [local tactic HexHermiteMathlib.Tactic.hermiteTac] extensionStub
attribute [local tactic HexHermiteMathlib.Tactic.hermiteTac] HexHermiteMathlib.Tactic.evalHermite

run_cmd do
  let handlers := (tacticElabAttribute.getEntries (← getEnv) ``HexHermiteMathlib.Tactic.hermiteTac).map (·.declName)
  unless handlers == [``HexHermiteMathlib.Tactic.evalHermite, ``extensionStub,
      ``HexHermiteMathlib.Tactic.evalHermite, ``HexHermiteMathlib.Tactic.hermiteFallback] do
    throwError "unexpected delegation handler order: {handlers}"

/-- info: structural extension -/
#guard_msgs in
example (h : True) : True := by hermite

/-- error: hermite: the vector is not a member; nonzero residual [1] -/
#guard_msgs in
example (h : (![1] : Fin 1 → ℤ) ∈ Submodule.span ℤ (Set.range !![2])) : (![1] : Fin 1 → ℤ) ∈ Submodule.span ℤ (Set.range !![2]) := by hermite

end Delegation

example : (![4, 12] : Fin 2 → ℤ) ∈
    Submodule.span ℤ (Set.range (Matrix.row !![2, 0; 0, 6])) := by hermite

section TermDelegation

private meta def termStub : Term.TermElab := fun _ _ => do
  logInfo "structural term extension"
  return Lean.mkNatLit 2

attribute [local term_elab HexHermiteMathlib.Tactic.hermiteTerm] termStub
attribute [local term_elab HexHermiteMathlib.Tactic.hermiteTerm] HexHermiteMathlib.Tactic.elabHermiteTerm

/-- info: structural term extension -/
#guard_msgs in
example : (hermite% (2 : ℕ)) = 2 := rfl

end TermDelegation

section ExtensionErrors

@[no_fallback]
private meta def extensionDecline : Tactic := fun _ =>
  throwError "hermite: test capability decline"

attribute [local tactic HexHermiteMathlib.Tactic.hermiteTac] extensionDecline

/-- error: hermite: test capability decline -/
#guard_msgs in
example : True := by hermite

end ExtensionErrors
