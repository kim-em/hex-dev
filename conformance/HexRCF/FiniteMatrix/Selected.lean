/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Signs
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Selected
open Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
elab "#finite_matrix_selected" : command => liftTermElabM do
  for (label, guarded) in [("canonical", false), ("guarded", true)] do
    let packet := mkConst (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Literals label)
    let reader ← mkAppM ``Read.selected #[toExpr guarded, mkConst ``Inputs.facts, packet,
      mkConst ``Packings.facts, mkConst ``Signs.facts]
    let _ ← restore (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Selected label) reader
#finite_matrix_selected
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Selected
