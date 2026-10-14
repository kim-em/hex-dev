/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import KernelReplay.FiniteBase
public import HexRealClosure.TowerContext
public meta import HexRealClosure.TowerContext
public import HexRealClosure.RecordPackets
public meta import HexRealClosure.RecordPackets
public meta import HexRealClosureMathlib.NativePackets

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativePacketsProbe
open Hex.SignDet

abbrev base := FiniteBaseProbe.base
abbrev E := BaseContext.Element base

private def binding : Tower.Signature := ⟨base.signature, []⟩
private def codec := BaseContext.Element.codec base
private def variablePoly : DensePoly E := DensePoly.ofCoeffs #[0, 1]

/-- An actual algebraic extension of two successive infinitesimals. Its
coefficient and predecessor types differ from the rational/Nat fixtures. -/
private def raw : RawDescriptor E Tower.Signature :=
  ⟨binding, variablePoly - DensePoly.C (FiniteBaseProbe.epsilon + FiniteBaseProbe.delta),
    .negInf, .posInf, [1], [1]⟩

/-- Compiled coverage of generic packet production and strict independent
readers. This test does not claim an ordinary-kernel root reconstruction. -/
private def check : Option Bool := do
  let root ← Descriptor.validate BaseContext.Element.sign binding raw
  let owner := Context.adjoin root (fun _ => false)
  let (claimed, scalar) ← (owner.buildSignPacket codec Tower.Signature.codec variablePoly).toOption
  let selected ← (Dag.decodeSigns codec Tower.Signature.codec root [owner.queryPoly variablePoly]
    #v[claimed] scalar.writeBytes).toOption
  let packed := owner.reduce raw.head
  let fact : SignFact owner := ⟨packed, owner.signPoly packed, rfl⟩
  let joint ← (owner.buildPackingPacket codec Tower.Signature.codec owner.reduce raw.head).toOption
  let record ← Packing.readPacket? codec Tower.Signature.codec owner.reduce rfl [fact] raw.head joint
  let missing := Packing.readPacket? codec Tower.Signature.codec owner.reduce rfl [] raw.head joint
  let changed := Packing.readPacket? codec Tower.Signature.codec owner.reduce rfl [fact]
    (raw.head + 1) joint
  let value := Element.ofPoly (context := owner) variablePoly
  let stored ← (ValueSign.buildPacket codec Tower.Signature.codec value).toOption
  let observed ← ValueSign.readPacket? codec Tower.Signature.codec value stored
  let changedValue := ValueSign.readPacket? codec Tower.Signature.codec
    (value + 1) stored
  let wrong : Tower.Signature := ⟨{ base.signature with infinitesimals := 1 }, []⟩
  let wrongOwner := Codec.readGraph codec Tower.Signature.codec wrong raw.head raw.lower raw.upper
    stored
  return claimed == 1 && selected.value == 1 && record.original == raw.head &&
    record.value == 0 && record.representative == packed && missing.isNone && changed.isNone &&
    observed.value == value && observed.value.polynomial == value.polynomial &&
    changedValue.isNone && wrongOwner.toOption.isNone

#guard check == some true

public meta section
open Lean Meta Elab Command

syntax (name := nativePacketsProbe) "#native_packets_probe" : command
@[command_elab nativePacketsProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let valueCodec := mkConst ``ValueCodec.rat
  let contextCodec := mkConst ``ValueCodec.nat
  let sign ← mkAppOptM ``Sturm.orderSign #[some (mkConst ``Rat), none, none, none, none]
  withLocalDeclD `owner (← mkAppM ``Context #[mkConst ``Rat, mkConst ``Nat,
      sign, toExpr (7 : Nat)]) fun owner => do
    let polynomial ← mkAppM ``DensePoly.C #[toExpr (1 : Rat)]
    let rejected ← try
      let _ ← NativePackets.sign valueCodec contextCodec owner polynomial
      pure false
    catch error =>
      unless (← error.toMessageData.toString) ==
          "native packet production requires complete closed input" do throw error
      pure true
    unless rejected do throwError "native producer accepted a local owner"
  logInfo "generic packet readers accepted a two-infinitesimal algebraic owner; incomplete production rejected"

#native_packets_probe

end

end Hex.RealClosure.Algebraic.KernelReplay.NativePacketsProbe
