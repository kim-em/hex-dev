/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Context
import HexRealClosureMathlib.FactReplay
import HexRCF.NestedTransport.Predecessor
import HexRCF.NestedTransport.SignLiterals
import HexRealClosureMathlib.FactReplay
import HexRCF.SelectedRoot.KernelCheck
import Lean.Elab.Command
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Signs
open Hex.RCF.RealCoefficients.NestedTransportTests.Context Data
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
def readAt (prior : List (Algebraic.SignFact Data.native)) :
    Option (Vector (Algebraic.SignFact Hex.RCF.RealCoefficients.NestedTransportTests.Context.native) 5) := do
  let value := Algebraic.Element.signCodec base.codec prior
  let ps ← (Codec.readList (Codec.readPoly value) Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals.polynomials).toOption
  let e ← (Algebraic.SignEvidence.codec value Signature.codec descriptor.raw).decode
    Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals.evidence |>.toOption
  Algebraic.Context.readEvidenceWith? original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign original.neg original.inv Hex.RCF.RealCoefficients.NestedTransportTests.Context.native
    (Algebraic.Element.cachedOne reduction reduction_eq prior)
    (Algebraic.Element.cachedAdd reduction reduction_eq prior)
    (Algebraic.Element.cachedNeg reduction reduction_eq prior)
    (Algebraic.Element.cachedSub reduction reduction_eq prior)
    (Algebraic.Element.cachedMul reduction reduction_eq prior)
    (Algebraic.Element.cachedInv reduction reduction_eq prior)
    (Algebraic.Element.cachedDiv reduction reduction_eq prior)
    (Algebraic.Element.cachedNatCast reduction reduction_eq prior)
    (Algebraic.Element.cachedOne_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedAdd_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedNeg_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedSub_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedMul_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedInv_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedDiv_eq reduction reduction_eq prior)
    (Algebraic.Element.cachedNatCast_eq reduction reduction_eq prior)
    ps e
    >>= fun facts => if h : ps.length = 5 then some (h ▸ facts) else none
meta section
open Lean Meta Elab Command
elab "#suffix_more_sign_check" : command => liftTermElabM do
  let result ← mkAppM ``readAt #[mkConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts]
  let proposition ← mkEq (← mkAppM ``Option.isSome #[result]) (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let proof := mkAppN (mkConst ``of_decide_eq_true)
    #[proposition, dictionary, ← mkEqRefl (mkConst ``Bool.true)]
  KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedTransportTests.Signs.accepted proposition proof
    #[``Descriptor.validate, ``Descriptor.ofReplay?]
end
#suffix_more_sign_check
#print axioms accepted
end Hex.RCF.RealCoefficients.NestedTransportTests.Signs
