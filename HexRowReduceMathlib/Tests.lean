/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRowReduceMathlib.Tactic

public section

namespace HexRowReduceMathlib.Tests

open HexMatrixMathlib

theorem inverse_product :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ) * !![-2, 1; 3 / 2, -1 / 2] = 1 := by inverse

theorem inverse_eq :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![-2, 1; 3 / 2, -1 / 2] := by inverse

theorem inverse_singular :
    (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = 0 := by inverse

noncomputable def inverse_value := inverse% (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ)
noncomputable def inverse_kernel := inverse% (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ)

theorem solve_residual :
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ).mulVec ![1, 1] = ![3, 7] := by solve

theorem solve_exists :
    ∃ x, (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℚ).mulVec x = ![3, 7] := by solve

theorem solve_inconsistent :
    ¬ ∃ x, (!![1, 0, 0; 1, 0, 0] : Matrix (Fin 2) (Fin 3) ℚ).mulVec x = ![0, 1] := by solve

noncomputable def solve_affine :=
  solve% (!![0, 1, 1] : Matrix (Fin 1) (Fin 3) ℚ) ![2]

noncomputable def solve_separator :=
  solve% (!![1, 0, 0; 1, 0, 0] : Matrix (Fin 2) (Fin 3) ℚ) ![0, 1]

theorem product_reverse :
    (1 : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1 / 2; 3, 1] * !![-2 / 3, 1 / 3; 2, 0] := by inverse

theorem inverse_reverse :
    (!![-2 / 3, 1 / 3; 2, 0] : Matrix (Fin 2) (Fin 2) ℚ) = !![0, 1 / 2; 3, 1]⁻¹ := by inverse

theorem zero_inverse : (0 : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = 0 := by inverse

theorem zero_literal_inverse :
    (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ = !![0, 0; 0, 0] := by inverse

theorem empty_inverse :
    (!![] : Matrix (Fin 0) (Fin 0) ℚ)⁻¹ = !![] := by inverse

noncomputable def empty_inverse_result := inverse% (!![] : Matrix (Fin 0) (Fin 0) ℚ)

theorem noncanonical_solution :
    (![2] : Fin 1 → ℚ) = (!![0, 1, 1] : Matrix (Fin 1) (Fin 3) ℚ).mulVec ![3, 0, 2] := by solve

theorem fraction_solution :
    (!![1 / 2, 1 / 3] : Matrix (Fin 1) (Fin 2) ℚ).mulVec ![2 / 3, 3 / 2] = ![5 / 6] := by solve

theorem no_rows_solution :
    (!![,,] : Matrix (Fin 0) (Fin 2) ℚ).mulVec ![3, 7] = ![] := by solve

theorem no_columns_solution :
    (!![;;] : Matrix (Fin 2) (Fin 0) ℚ).mulVec ![] = ![0, 0] := by solve

theorem no_columns_inconsistent :
    ¬ ∃ x, (!![;;] : Matrix (Fin 2) (Fin 0) ℚ).mulVec x = ![0, 1] := by solve

noncomputable def empty_solve := solve% (!![] : Matrix (Fin 0) (Fin 0) ℚ) ![]
noncomputable def no_rows_solve := solve% (!![,,] : Matrix (Fin 0) (Fin 2) ℚ) ![]
noncomputable def no_columns_solve := solve% (!![;;] : Matrix (Fin 2) (Fin 0) ℚ) ![0, 0]
noncomputable def zero_solve := solve% (0 : Matrix (Fin 2) (Fin 3) ℚ) (0 : Fin 2 → ℚ)

example : (Matrix.of ![![1, 2], ![3, 4]] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ =
    !![-2, 1; 3 / 2, -1 / 2] := by inverse

example : (Matrix.ofArray (m := 2) (n := 2) #[1, 2, 3, 4] rfl : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ =
    !![-2, 1; 3 / 2, -1 / 2] := by inverse

def functionMatrix : Matrix (Fin 2) (Fin 2) ℚ := fun i j => if i = j then 2 else 0

example : functionMatrix⁻¹ =
    !![1 / 2, 0; 0, 1 / 2] := by inverse

example : (Matrix.ofArray (m := 1) (n := 2) #[1, 2] rfl : Matrix (Fin 1) (Fin 2) ℚ).mulVec
    (fun i => if i = 0 then 1 else 2) = (fun _ => 5) := by solve

example : (Matrix.of ![![1, 2]] : Matrix (Fin 1) (Fin 2) ℚ).mulVec ![1, 2] = ![5] := by solve

noncomputable def inferred_inverse := inverse% !![1 / 2, 0; 0, 1 / 3]
noncomputable def inferred_solve := solve% !![1 / 2, 1 / 3] ![1 / 2]

def solve (x : Nat) := x + 1
def inverse (x : Nat) := x + 2
example : solve 2 = 3 := rfl
example : inverse 2 = 4 := rfl

theorem affine_coordinates (x : Fin 3 → ℚ) :
    (!![0, 1, 1] : Matrix (Fin 1) (Fin 3) ℚ).mulVec x = ![2] ↔
      ∃! c : Fin 2 → ℚ, x = ![0, 2, 0] + (!![1, 0; 0, -1; 0, 1] : Matrix (Fin 3) (Fin 2) ℚ).mulVec c := by
  have h := SolveResult.spec solve_affine
  dsimp only [SolveResult.statement, solve_affine] at h
  exact h x

open Lean Elab Tactic

run_cmd Command.liftTermElabM do
  let matrixType ← Term.elabType (← `(Matrix (Fin 2) (Fin 2) ℚ))
  let A ← Meta.mkFreshExprMVar matrixType
  match ← HexRowReduceMathlib.Tactic.readMatrix A with
  | .notApplicable => pure ()
  | _ => throwError "numeric matrix recognition claimed an unresolved metavariable"
  if ← A.mvarId!.isAssigned then
    throwError "numeric matrix recognition assigned an unresolved metavariable"

run_cmd Command.liftTermElabM do
  let vectorType ← Term.elabType (← `(Fin 2 → ℚ))
  let v ← Meta.mkFreshExprMVar vectorType
  match ← HexRowReduceMathlib.Tactic.readVector v with
  | .notApplicable => pure ()
  | _ => throwError "numeric vector recognition claimed an unresolved metavariable"
  if ← v.mvarId!.isAssigned then
    throwError "numeric vector recognition assigned an unresolved metavariable"

run_cmd do
  for name in [``inverse_product, ``inverse_eq, ``inverse_singular, ``inverse_value,
      ``inverse_kernel, ``solve_residual, ``solve_exists, ``solve_inconsistent,
      ``solve_affine, ``solve_separator, ``empty_inverse, ``empty_inverse_result,
      ``empty_solve, ``no_rows_solve, ``no_columns_solve, ``zero_solve, ``affine_coordinates] do
    for axiomName in ← Lean.collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unexpected axiom in {name}: {axiomName}"

/-- info: 'HexRowReduceMathlib.Tests.solve_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solve_residual

/-- error: inverse: declined: certified singular matrix; nonzero kernel vector [-2, 1] -/
#guard_msgs in
example : (!![1, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, 0; 0, 0] = 1 := by inverse

/-- error: inverse: declined: the stated inverse is false; computed inverse [[1/2]] -/
#guard_msgs in
example : (!![2] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![1] := by inverse

/-- error: solve: declined: incorrect candidate; residual [-1]; particular solution [2] -/
#guard_msgs in
example : (!![1] : Matrix (Fin 1) (Fin 1) ℚ).mulVec ![1] = ![2] := by solve

/-- error: solve: declined: certified inconsistent system; separator [-1, 1]; yᵀA = 0, yᵀb = 1 ≠ 0 -/
#guard_msgs in
example : ∃ x, (!![1, 0, 0; 1, 0, 0] : Matrix (Fin 2) (Fin 3) ℚ).mulVec x = ![0, 1] := by solve

/-- error: inverse: not applicable: expected A * B = 1 or A⁻¹ = B over ℚ, in either orientation -/
#guard_msgs in
example : ((fun i j : Fin 2 => if i = j then (2 : ℚ) else 0) : Matrix (Fin 2) (Fin 2) ℚ)⁻¹ =
    !![1 / 2, 0; 0, 1 / 2] := by inverse

run_cmd do
  for (kind, expected) in [
      (``HexRowReduceMathlib.Tactic.inverseTac,
        [``HexRowReduceMathlib.Tactic.evalInverse, ``HexRowReduceMathlib.Tactic.inverseFallback]),
      (``HexRowReduceMathlib.Tactic.solveTac,
        [``HexRowReduceMathlib.Tactic.evalSolve, ``HexRowReduceMathlib.Tactic.solveFallback])] do
    let handlers := (tacticElabAttribute.getEntries (← getEnv) kind).map (·.declName)
    unless handlers == expected do
      throwError "unexpected shipped handler order: {handlers}"

section Delegation

@[no_fallback] private meta def extensionStub : Tactic := fun _ => do
  logInfo "row reduction extension"
  evalTactic (← `(tactic| assumption))

attribute [local tactic HexRowReduceMathlib.Tactic.inverseTac] extensionStub
attribute [local tactic HexRowReduceMathlib.Tactic.inverseTac] HexRowReduceMathlib.Tactic.evalInverse
attribute [local tactic HexRowReduceMathlib.Tactic.solveTac] extensionStub
attribute [local tactic HexRowReduceMathlib.Tactic.solveTac] HexRowReduceMathlib.Tactic.evalSolve

/-- info: row reduction extension -/
#guard_msgs in
example (h : True) : True := by inverse

/-- info: row reduction extension -/
#guard_msgs in
example (h : True) : True := by solve

/-- error: inverse: declined: the stated inverse is false; computed inverse [[1/2]] -/
#guard_msgs in
example (h : (!![2] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![1]) :
    (!![2] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![1] := by inverse

end Delegation

section TermDelegation

private meta def termStub : Term.TermElab := fun _ _ => do
  logInfo "row reduction term extension"
  return Lean.mkNatLit 2

attribute [local term_elab HexRowReduceMathlib.Tactic.inverseTerm] termStub
attribute [local term_elab HexRowReduceMathlib.Tactic.inverseTerm] HexRowReduceMathlib.Tactic.elabInverseTerm
attribute [local term_elab HexRowReduceMathlib.Tactic.solveTerm] termStub
attribute [local term_elab HexRowReduceMathlib.Tactic.solveTerm] HexRowReduceMathlib.Tactic.elabSolveTerm

/-- info: row reduction term extension -/
#guard_msgs in
example : (inverse% (2 : ℕ)) = 2 := rfl

/-- info: row reduction term extension -/
#guard_msgs in
example : (solve% (2 : ℕ) (3 : ℕ)) = 2 := rfl

end TermDelegation

example : Hex.Matrix.checkInverseList 1 [[2]]
    (.invertible ⟨1, [[2]]⟩ ⟨1, [[1]]⟩) = false := by decide +kernel

example : Hex.Matrix.checkInverseList 1 [[0]]
    (.singular ⟨1, [[0]]⟩ ⟨1, [0]⟩ 0) = false := by decide +kernel

example : Hex.Matrix.checkSolutionList 1 1 [[2]] [1] [1] = false := by decide +kernel

example : Hex.Matrix.checkSolveList 1 1 [[0]] [1]
    (.inconsistent ⟨1, [[0]]⟩ ⟨1, [1]⟩ ⟨1, [0]⟩) = false := by decide +kernel

end HexRowReduceMathlib.Tests
