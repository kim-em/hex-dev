/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Sparse.Kernel
public import HexGraph.Sparse.Build
public meta import Lean

open Hex Hex.GraphIso

meta section
open Lean Elab Tactic Meta
-- Assign the replay proof without asking elaborator transparency to unfold
-- another module's implementation; the kernel checks the complete term.
elab "sparse_kernel_decide" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let prop ← goal.getType
    let inst ← synthInstance (← mkAppM ``Decidable #[prop])
    let app := mkApp2 (mkConst ``Decidable.decide) prop inst
    let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let expected ← mkAppM ``Eq #[app, mkConst ``Bool.true]
    let proof ← mkExpectedTypeHint refl expected
    goal.assign (mkApp3 (mkConst ``of_decide_eq_true) prop inst proof)
  replaceMainGoal []

end

-- A non-identity literal transporter, consumed through the public proof
-- surface in a different module. The middle row's images need sorting.
private def pathA : Sparse.Colored 3 1 :=
  ⟨SparseGraph.ofEdges [(0, 1), (1, 2)], Coloring.trivial 3⟩
private def pathB : Sparse.Colored 3 1 :=
  ⟨SparseGraph.ofEdges [(1, 2), (2, 0)], Coloring.trivial 3⟩
private def cycle3 : Perm 3 := Perm.ofFn (fun i => ⟨(i.val + 1) % 3, by omega⟩)
  (by intro i j h; apply Fin.ext; have hv := congrArg Fin.val h; dsimp at hv; omega)
  (by intro i; refine ⟨⟨(i.val + 2) % 3, by omega⟩, ?_⟩; apply Fin.ext; dsimp; omega)

private theorem pathRowsA : Sparse.Kernel.rows pathA.graph = [[1], [0, 2], [1]] := by
  sparse_kernel_decide
private theorem pathRowsB : Sparse.Kernel.rows pathB.graph = [[2], [2], [0, 1]] := by
  sparse_kernel_decide
private theorem pathCheck : Sparse.Kernel.checkIso 3 [[1], [0, 2], [1]] [[2], [2], [0, 1]]
    [0, 0, 0] [0, 0, 0] [1, 2, 0] = true := by
  sparse_kernel_decide

example : Sparse.IsIso pathA pathB cycle3 :=
  Sparse.Kernel.isIso_of_checkIso
    pathRowsA pathRowsB
    (show pathA.coloring.cells.toList.map Fin.val = [0, 0, 0] by sparse_kernel_decide)
    (show pathB.coloring.cells.toList.map Fin.val = [0, 0, 0] by sparse_kernel_decide)
    (show cycle3.vec.toList.map Fin.val = [1, 2, 0] by sparse_kernel_decide)
    pathCheck

example : Sparse.Kernel.checkIso 0 [] [] [] [] [] = true := by sparse_kernel_decide

example : Sparse.Kernel.checkIso 3 [[1], [0, 2], [1]] [[2], [2], [0, 1]]
    [0, 0, 0] [0, 0, 0] [0, 1, 2] = false := by sparse_kernel_decide

example : Sparse.Kernel.checkIso 3 [[1], [0, 2], [1]] [[2], [2], [0, 1]]
    [0, 0, 0] [0, 1, 0] [1, 2, 0] = false := by sparse_kernel_decide

example : Sparse.Kernel.checkIso 3 [[1], [0, 2], [1]] [[2], [2, 2], [0, 1]]
    [0, 0, 0] [0, 0, 0] [1, 2, 0] = false := by sparse_kernel_decide
