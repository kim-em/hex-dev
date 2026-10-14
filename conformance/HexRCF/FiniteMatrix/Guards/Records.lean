/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Literals
import HexRCF.FiniteMatrix.Guards.Read
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
elab "#frozen_guard_records" : command => liftTermElabM do
  let extra ← mkAppM ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Read.sign #[mkConst ``Inputs.facts, mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Literals.extraSign]
  let extra ← restore `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.extra extra
  let list ← mkListLit (← inferType extra) [extra]
  retain `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.facts (← mkAppM ``List.append #[mkConst ``Signs.facts, list])
  for (name, zero, packet) in [("positive", false, ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Literals.positive),
      ("zero", true, ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Literals.zero)] do
    let reader := mkAppN (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Read.selected)
      #[toExpr zero, mkConst ``Inputs.facts, mkConst packet, mkConst ``Packings.facts, mkConst `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.facts]
    let _ ← restore (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records name) reader

#frozen_guard_records
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records
