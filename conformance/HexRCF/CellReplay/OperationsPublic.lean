/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public section
namespace Hex.RCF.RealCoefficients.CellReplayTests.OperationsPublic
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Public module clients need no private reader body to transport acceptance
or use the actual real soundness theorem. -/
theorem source (model : Model parent ℝ)
    (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier)
    (rootGraph cells : Codec.Json)
    (accepted : CellOperations.check operations value values formula guards cert quantifier rootGraph cells = .ok true) :
    (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
      (fun i => model.value (values i)) :=
  CellOperations.check_sound model operations value values formula guards cert quantifier rootGraph cells accepted

/-- An original zero divisor precedes both malformed packets at the public
import boundary, independently of every preceding guard or coefficient. -/
theorem late_zero (operations : Hex.RealClosure.Replay.Operations parent.sign)
    (value : ValueCodec parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (first : parent.Value)
    (cert : RadicalCert parent.Value Signature) (quantifier : RealFormula.Quantifier) :
    CellOperations.check operations value values formula [first,0] cert quantifier
      Codec.Json.Value.null Codec.Json.Value.null = .error .divisor := by
  rw [CellOperations.check_eq]
  unfold CompleteReplay.check CompleteReplay.read
  rw [RootReplay.read_zero value [first,0] cert.core .negInf .posInf Codec.Json.Value.null
    0 (by simp) rfl]
  rfl

#print axioms source
#print axioms late_zero
end Hex.RCF.RealCoefficients.CellReplayTests.OperationsPublic
