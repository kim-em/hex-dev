/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Restore
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Inputs
open Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
meta section
elab "#finite_matrix_scalar" : command => liftTermElabM do
  let mut records : List Expr := []
  for i in [:31] do
    let packet := mkConst (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Literals s!"scalar{i}")
    let reader ← mkAppM ``Read.scalar #[packet]
    let record ← restore (Name.num `Hex.RCF.RealCoefficients.FiniteMatrixTests.Inputs.record i) reader
    records := records ++ [record]
  let type ← mkAppM ``SignFact #[mkConst ``FiniteTower.first]
  retain `Hex.RCF.RealCoefficients.FiniteMatrixTests.Inputs.facts (← mkListLit type records)
end
#finite_matrix_scalar
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Inputs
