/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Schema
import HexRCF.FiniteMatrix.Binding
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Meaning
open Hex Hex.RealClosure Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem generator : Semantics.read FiniteTower.generator = Real.sqrt 2 := by
  have identity := congrFun Hex.RCF.RealCoefficients.FiniteMatrixTests.Binding.valuation_eq (0 : Fin 1)
  simpa [Hex.RCF.RealCoefficients.FiniteMatrixTests.Binding.valuation, Hex.RCF.RealCoefficients.FiniteMatrixTests.Schema.values, RealFormula.append] using identity

theorem values (entries : List (Packing FiniteTower.first)) :
    (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive entries).map Semantics.read = [Real.sqrt 2 - 1, -1] := by
  unfold Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.positive
  erw [Element.replayOne_eq, Element.replaySub_eq, Element.replayNeg_eq]
  change [Semantics.read (FiniteTower.generator - 1), Semantics.read (-1)] = _
  rw [Semantics.closed.read_sub _ _ trivial trivial, Semantics.negative,
    Semantics.closed.read_one, generator]

end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Meaning
