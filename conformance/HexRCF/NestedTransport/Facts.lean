/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Restore
import HexRCF.NestedTransport.Constants
import HexRCF.NestedTransport.Predecessor
import HexRCF.NestedTransport.SignLiterals
import HexRealClosureMathlib.FactReplay
import HexRCF.SelectedRoot.KernelCheck
import Lean.Elab.Command
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Facts
open Hex.RCF.RealCoefficients.NestedTransportTests.Context Data
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
def parsedAt (prior : List (Algebraic.SignFact Data.native)) : Option (List (DensePoly Data.parent.Value) ×
    Algebraic.SignEvidence Data.parent.Value Signature) := do
  let value := Algebraic.Element.signCodec base.codec prior
  let ps ← (Codec.readList (Codec.readPoly value) Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals.polynomials).toOption
  let e ← (Algebraic.SignEvidence.codec value Signature.codec descriptor.raw).decode
    Hex.RCF.RealCoefficients.NestedTransportTests.SignLiterals.evidence |>.toOption
  return (ps,e)
def parsed := parsedAt Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts
meta section
open Lean Meta Elab Command
elab "#suffix_restore_some " term:term " => " name:ident : command => liftTermElabM do
  let result ← Term.elabTerm term none
  let proposition ← mkEq (← mkAppM ``Option.isSome #[result]) (mkConst ``Bool.true)
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let proof := mkAppN (mkConst ``of_decide_eq_true)
    #[proposition, dictionary, ← mkEqRefl (mkConst ``Bool.true)]
  KernelCheck.addChecked ((← getCurrNamespace) ++ name.getId) proposition proof
    #[``Descriptor.validate, ``Descriptor.ofReplay?]
end
#suffix_restore_some parsed => parsed_ok
def polynomials := (parsed.get parsed_ok).1
private theorem count : polynomials.length = 5 := by decide +kernel
def evidence := (parsed.get parsed_ok).2
def read :=
  let prior := Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts
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
    polynomials evidence
#suffix_restore_some read => read_ok
private theorem canonical : read = native.readEvidence? original.value original.zero_iff
    original.one original.add original.sub original.mul original.nat original.sign
    original.neg original.inv polynomials evidence := by
  unfold read
  exact Algebraic.Context.readEvidenceWith_eq original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign original.neg original.inv Hex.RCF.RealCoefficients.NestedTransportTests.Context.native
    (Algebraic.Element.cachedOne reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedNeg reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedSub reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedMul reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedInv reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedDiv reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedOne_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedAdd_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedNeg_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedSub_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedMul_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedInv_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedDiv_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    (Algebraic.Element.cachedNatCast_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    polynomials evidence
def fact (i : Fin polynomials.length) : Algebraic.SignFact Hex.RCF.RealCoefficients.NestedTransportTests.Context.native :=
  Hex.RCF.RealCoefficients.NestedTransportTests.Restore.restore polynomials evidence
    (by rw [← canonical]; exact read_ok) i
def first := fact ⟨0, by decide +kernel⟩
def second := fact ⟨1, by decide +kernel⟩
def third := fact ⟨2, by decide +kernel⟩
def fourth := fact ⟨3, by decide +kernel⟩
def fifth := fact ⟨4, by decide +kernel⟩
def facts := [first,second,third,fourth,fifth,
  Hex.RCF.RealCoefficients.NestedTransportTests.Constants.constant (@One.one Data.parent.Value
    (Algebraic.Element.cachedOne reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)),
  Hex.RCF.RealCoefficients.NestedTransportTests.Constants.constant (@NatCast.natCast Data.parent.Value
    (Algebraic.Element.cachedNatCast reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts) 2)]
end Hex.RCF.RealCoefficients.NestedTransportTests.Facts
