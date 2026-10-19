/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Data
import HexRCF.FiniteMatrix.Guards.Mutations
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Refusals
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
elab "#frozen_guard_refusals" : command => liftTermElabM do
  for (label, packet) in [("order", ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Mutations.order),
      ("context", ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Mutations.context), ("cycle", ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Mutations.cycle)] do
    let reader := mkAppN (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Read.selected)
      #[toExpr false, mkConst ``Inputs.facts, mkConst packet, mkConst ``Packings.facts, mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.facts]
    let goal ← mkEq (← mkAppM ``Option.isNone #[reader]) (mkConst ``Bool.true)
    Hex.RCF.SelectedRootTests.KernelCheck.addChecked (Name.str `Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Refusals label) goal
      (← mkDecideProof goal) #[``Hex.SignDet.Descriptor.validate, ``Hex.SignDet.Descriptor.ofReplay?]
      #[``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Read.selected]
#frozen_guard_refusals

elab "#frozen_guard_missing" : command => liftTermElabM do
  let reader := mkAppN (mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Read.selected)
    #[toExpr false, mkConst ``Inputs.facts, mkConst ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Literals.positive, mkConst ``Packings.facts,
      mkConst ``Signs.facts]
  let goal ← mkEq (← mkAppM ``Option.isSome #[reader]) (mkConst ``Bool.true)
  let decision ← mkDecide goal
  let result ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) decision)
  if result.isConstOf ``Bool.true || result.isConstOf ``Bool.false then
    throwError "missing extra sign reached a Boolean"
  let statement ← mkEq decision (mkConst ``Bool.true)
  let options ← getOptions
  let proof ← mkEqRefl (mkConst ``Bool.true)
  let declarationName ← mkFreshUserName `missingStoredSign
  let checked := (← getEnv).addDeclCore (Core.getMaxHeartbeats options).toUSize
    (maxRecDepth.get options).toUSize (.thmDecl {
      name := declarationName, levelParams := [], type := statement, value := proof}) none (doCheck := true)
  match checked with
  | .error (.declTypeMismatch ..) => pure ()
  | .error error => throwKernelException error
  | .ok _ => throwError "unrecorded stored sign accepted"
#frozen_guard_missing
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Refusals
