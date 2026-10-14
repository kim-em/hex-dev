/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.FiniteOperands
public meta import HexRealClosureTheory.FiniteOperands
import all HexPoly.Dense
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteOperandsProbe

@[expose] def left : DensePoly Rat := DensePoly.ofCoeffs #[1, 2]
@[expose] def right : DensePoly Rat := DensePoly.ofCoeffs #[-1, -2]

public meta section
open Lean Meta Elab Command

syntax (name := finiteOperandsProbe) "#finite_operands_probe" : command
@[command_elab finiteOperandsProbe]
def elaborate : CommandElab := fun _ => liftTermElabM do
  let readerType ← mkArrow (mkConst ``Rat) (mkConst ``Real)
  let obligations ← withLocalDeclD `read readerType fun read => do
    let type ← mkAppM ``Transport.Sum #[read, mkConst ``left, mkConst ``right]
    FiniteData.inputs type (fun _ => pure none)
  unless obligations.size == 1 do throwError "cancelling sum did not retain its reached operation"
  let some leaf := obligations[0]? | throwError "cancelling sum lost its operands"
  let some support ← leaf.coefficients? | throwError "cancelling sum lost its source coefficients"
  if support.hasFVar then throwError "coefficient support depends on the unchosen reader"
  let expected ← Elab.Term.elabTerm (← `(([1, 2, -1, -2] : List Rat))) none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let type ← mkEq support expected
  let proof ← mkEqRefl support
  let _ ← auditProof proof type
  kernelCheck `__finiteOperandsCancellation type proof
  addDecl (.thmDecl {
    name := `Hex.RealClosure.Algebraic.KernelReplay.FiniteOperandsProbe.cancellationInputs
    levelParams := [], type, value := proof })
  let size ← mkAppM ``DensePoly.size #[← mkAppM ``HAdd.hAdd #[mkConst ``left, mkConst ``right]]
  kernelCheck `__finiteOperandsZeroOutput (← mkEq size (toExpr (0 : Nat))) (← mkEqRefl size)
  logInfo "cancellation retains all four source coefficients before choosing a reader; output has no coefficients"

end

/-- info: cancellation retains all four source coefficients before choosing a reader; output has no coefficients -/
#guard_msgs in
#finite_operands_probe

end Hex.RealClosure.Algebraic.KernelReplay.FiniteOperandsProbe
