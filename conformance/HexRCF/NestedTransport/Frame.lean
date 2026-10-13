/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootTransportConformance
import HexRCF.NestedTransport.Literals
import HexSignDet.DagEncode
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Frame
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
def descriptor := RootTransportConformance.checked.converted
def fields := (Codec.tuple 6 Hex.RCF.RealCoefficients.NestedTransportTests.Literals.subject).toOption
private theorem fields_some : fields.isSome = true := by decide +kernel
def signatureRead := Signature.codec.decode (fields.get fields_some)[0]
private theorem signature_some : signatureRead.toOption.isSome = true := by decide +kernel
def signature := signatureRead.toOption.get signature_some
private theorem bound : 1 < signature.roots.length := by decide +kernel
def frame := signature.roots[1]'bound
private theorem leaf : descriptor.evidence = .leaf descriptor.evidence.node := by
  have shape : (match descriptor.evidence with
    | .leaf _ => true | .split _ _ _ => false) = true := by decide +kernel
  cases he : descriptor.evidence with
  | leaf node => rfl
  | split node left right => simp only [he, Bool.false_eq_true] at shape
private theorem literal : rootData RootTransportData.conversion.context.codec descriptor = frame.toJson := by
  -- These instances are needed when elaborating Data.encodeLeaf below.
  let : Hashable RootTransportData.conversion.context.Value := ⟨fun a => hash (RootTransportData.conversion.context.codec.encode a)⟩
  let : Hashable Signature := ⟨fun _ => 0⟩
  unfold rootData
  dsimp only
  rw [leaf, Data.encodeLeaf]
  decide +kernel
theorem encoded : Literal.ofJson (rootData RootTransportData.conversion.context.codec descriptor) = some frame := by
  rw [literal, Literal.ofJson_toJson]
#print axioms encoded
end Hex.RCF.RealCoefficients.NestedTransportTests.Frame
