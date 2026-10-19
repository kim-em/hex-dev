/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTowerUse
public meta import KernelReplay.FiniteTowerUse
public meta import HexRealClosureTheory.NativePackets
public meta import HexRealClosureTheory.NativeCodecs
public import HexRealClosure.SignCodec
import all HexRealClosure.Algebraic
import all HexRealClosure.SignCodec
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexPoly.Dense
import all Init.Data.Array.Basic
import all Init.Data.Rat.Basic

import all HexRealClosure.InversePacking
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Euclid.DivGcd
import all HexRealClosure.Packing
import all HexRealClosure.ValueSigns
import all HexRealClosure.RecordPackets
import all HexRealClosure.InversePackets
import all HexSignDet.Dag
import all HexSignDet.Thom
import all HexSignDet.Replay
import all HexSignDet.MomentReplay
import all HexSignDet.QueryReduction
import all HexSignDet.Reduction
import all HexSignDet.Matrix
import all HexRank.Cert
import all HexMatrix.MatrixAlgebra

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeChildrenProbe
open Lean Meta Elab Command Hex.SignDet FiniteData FiniteTower

syntax (name := nativeChildrenProbe) "#native_children_probe" : command
@[command_elab nativeChildrenProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let owner := mkConst ``first
  let upper := mkConst ``FiniteTowerUse.next
  let rat := mkConst ``ValueCodec.rat
  let nat := mkConst ``ValueCodec.nat
  let element ← mkAppM ``Element #[owner]
  let codec ← mkAppOptM ``Element.codec (element.getAppArgs.map some ++ #[some rat])
  let zero ← mkAppOptM ``Zero.zero #[some element, none]
  let one ← mkAppOptM ``One.one #[some element, none]
  let polynomial ← mkAppM ``DensePoly.ofCoeffs #[← mkArrayLit element [zero, one]]
  let (claimed, packet) ← NativePackets.sign codec nat upper polynomial #[owner, upper]
  unless claimed == 1 do throwError "native nested generator sign changed"
  let children ← NativePackets.children rat nat upper (jsonExpr packet)
  let fields ← match children.getArr? with
    | .ok fields => pure fields
    | .error error => throwError "child packet output: {error}"
  unless !fields.isEmpty do throwError "native child discovery omitted all nonzero coefficients"
  let retained : NativeOwner := ⟨owner, rat, nat, mkConst ``reduction,
    mkConst ``reduction_eq, fun polynomial claimed packet =>
      mkAppM ``RationalRoot.readFact? #[owner, polynomial, claimed, packet]⟩
  let upperReduction ← mkAppM ``Context.reduce #[upper]
  let upperOwner : NativeOwner := ⟨upper, codec, nat, upperReduction,
    ← mkEqRefl upperReduction, fun _ _ _ => throwError "upper scalar reader unused"⟩
  let factory : NativeFactory := ⟨#[retained, upperOwner]⟩
  let codecs : NativeCodecs := ⟨factory, rat, fun index _ polynomial claimed packet => do
    unless index == 0 do throwError "fixture scalar reader only covers its base owner"
    mkAppM ``RationalRoot.readFact? #[owner, polynomial, claimed, packet]⟩
  let strict ← codecs.graph 1 packet
  let pair ← match fields[0]!.getArr? with
    | .ok pair => pure pair
    | .error error => throwError "child packet fields: {error}"
  let tag ← match Codec.Json.decode (α := Int) pair[1]! with
    | .ok tag => pure tag
    | .error error => throwError "child packet tag: {error}"
  try
    let _ ← codecs.values 1 #[Codec.Json.arr #[pair[0]!, Codec.Json.of (-tag)]]
    throwError "wrong stored child sign was accepted"
  catch error =>
    unless (← error.toMessageData.toString).contains
        "stored coefficient sign disagrees with native packet" do throw error
  let root ← mkAppM ``Context.root #[upper]
  let raw ← mkAppM ``Descriptor.raw #[root]
  let graph ← mkAppM ``Codec.readGraph #[strict, nat,
    ← mkAppM ``RawDescriptor.context #[raw], ← mkAppM ``RawDescriptor.head #[raw],
    ← mkAppM ``RawDescriptor.lower #[raw], ← mkAppM ``RawDescriptor.upper #[raw], jsonExpr packet]
  let _ ← checkedRecord (← mkAppM ``Except.toOption #[graph])
  logInfo m!"recursive native codec supplied {fields.size} independently checked scalar keys for strict nested graph decoding; changed child signs rejected; no native proof objects exported"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
#native_children_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeChildrenProbe
