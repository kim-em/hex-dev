/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Packings
import HexRCF.FiniteMatrix.Inputs
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Signs
open Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
meta section
elab "#finite_matrix_sign" : command => liftTermElabM do
  let mut records : List Expr := []
  for i in [:21] do
    let packet := mkConst (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Literals s!"sign{i}")
    let reader ← mkAppM ``Read.sign #[mkConst ``Inputs.facts, packet]
    let record ← restore (Name.num `Hex.RCF.RealCoefficients.FiniteMatrixTests.Signs.record i) reader
    records := records ++ [record]
  let type ← mkAppM ``ValueSign #[mkConst ``FiniteTower.first]
  retain `Hex.RCF.RealCoefficients.FiniteMatrixTests.Signs.facts (← mkListLit type records)
end
#finite_matrix_sign
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Signs
