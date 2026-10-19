/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Reader
import HexRCF.FiniteMatrix.Guards.Quotient.Literals
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Records
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
elab "#frozen_quotient_records" : command => liftTermElabM do
  let packing ← restore `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Records.packing
    (← mkAppM ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Read.packing #[mkConst ``Literals.packing])
  let list ← mkListLit (← inferType packing) [packing]
  retain `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Records.entries
    (← mkAppM ``List.append #[mkConst ``Packings.facts, list])
  let _ ← restore `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Records.inverse
    (← mkAppM ``Reader.read #[mkConst ``Reader.argument, mkConst ``Reader.entry,
      mkConst ``Literals.inverseGraph])
  let _ ← restore `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Records.alternate
    (← mkAppM ``Reader.read #[← mkAppM ``Packing.value #[mkConst ``Reader.entry],
      mkConst ``Reader.alternate, mkConst ``Literals.alternateGraph])
#frozen_quotient_records
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Records
