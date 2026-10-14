/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTower
public meta import KernelReplay.FiniteTower
public meta import HexRealClosureTheory.NativeFactory
public meta import HexRealClosureTheory.NativeReaders
import all HexRealClosure.InversePacking
import all HexRealClosure.Algebraic
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic
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
import all HexRealClosure.RecordReaders
import all HexRealClosure.QueryOperations
import all HexRealClosure.RecordQueries

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeReadersProbe
open Lean Meta Elab Command Hex.SignDet FiniteData FiniteTower

private def checkBinding (name : Name) (value expected : Expr) : MetaM Unit := do
  let type ← mkEq value expected
  let proof ← mkEqRefl expected
  let _ ← auditProof proof type
  kernelCheck name type proof

syntax (name := nativeReadersProbe) "#native_readers_probe" : command
@[command_elab nativeReadersProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let context := mkConst ``first
  let codec := mkConst ``ValueCodec.rat
  let ctx := mkConst ``ValueCodec.nat
  let ownerType ← withTransparency .all (whnf (← inferType context))
  let sign := ownerType.getAppArgs[ownerType.getAppArgs.size - 2]!
  let operations ← NativeOperations.native (mkConst ``Rat) sign
  let (reduce, reduceEq) ← operations.reduction context
  let owner : NativeOwner := ⟨context, codec, ctx, reduce, reduceEq,
    fun polynomial claimed packet =>
      mkAppM ``RationalRoot.readFact? #[context, polynomial, claimed, packet]⟩
  let factory : NativeFactory := ⟨#[owner]⟩
  for polynomial in #[mkConst ``variablePoly, ← mkAppM ``RawDescriptor.head
      #[← mkAppM ``Descriptor.raw #[← mkAppM ``Context.root #[context]]]] do
    let fact ← factory.scalar owner (mkApp reduce polynomial)
    let facts ← mkListLit (← mkAppM ``SignFact #[context]) [fact]
    let packet ← NativePackets.packing codec ctx context reduce polynomial #[context]
    let entry ← checkedRecord (← operations.packingReader context codec ctx reduce reduceEq
      facts polynomial (jsonExpr packet))
    checkBinding `__nativePackingOriginal (← mkAppM ``Packing.original #[entry]) polynomial
    let value ← mkAppM ``Packing.value #[entry]
    let packet ← NativePackets.storedSign codec ctx value #[context]
    let record ← checkedRecord (← operations.valueSignReader context codec ctx value (jsonExpr packet))
    checkBinding `__nativeStoredOperand (← mkAppM ``ValueSign.value #[record]) value
  let argument := mkConst ``generator
  let core ← operations.core
  let candidate ← mkAppM ``Element.inverseOperations #[core, argument]
  let entry ← factory.packing owner candidate
  let result ← mkAppM ``Packing.value #[entry]
  let packet ← NativePackets.inverse codec ctx context argument result #[context]
  let inverse ← checkedRecord (← operations.inverseReader context codec ctx argument entry (jsonExpr packet))
  checkBinding `__nativeInverseOriginal (← mkAppM ``Packing.Inverse.argument
    #[← mkAppM ``InverseFact.inverse #[inverse]]) argument
  logInfo "cached record readers checked original generator and canonical-zero packings, stored operands and native inverse candidate with the ordinary kernel"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
#native_readers_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeReadersProbe
