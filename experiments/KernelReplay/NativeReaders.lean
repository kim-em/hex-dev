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
public import HexRealClosureTheory.FiniteSupport
public meta import HexRealClosureTheory.FiniteSupport
public meta import HexRealClosureTheory.NativeBatch
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

private unsafe def checkLookup (finder : Name) (record key : Expr) : MetaM Unit := do
  let empty ← mkListLit (← inferType record) []
  let found ← mkAppM finder #[empty, key]
  let type ← mkEq (← mkAppM ``Option.isSome #[found]) (mkConst ``Bool.true)
  let leaf : Leaf := ⟨type, ← getLCtx, ← getLocalInstances⟩
  let some lookup ← leaf.lookup? | throwError "native record lookup was not recognized"
  let (_, some known) ← lookup.insertKnown record #[⟨empty⟩]
    | throwError "closed native record binding was not retained"
  kernelCheck `__nativeLookupHead known.lookup.leaf.type known.proof
  let inventory ← mkAppM ``List.cons #[record, known.lookup.inventory]
  let target := known.lookup.withInventory inventory
  let some proof ← known.find? target | throwError "native record lookup was not lifted"
  unless (← inferType proof) == target.leaf.type do
    throwError "native record lookup changed its exact statement"
  let _ ← auditProof proof target.leaf.type
  kernelCheck `__nativeLookupCons target.leaf.type proof
  let prepared ← NativeBatch.prepare #[known.lookup.leaf, target.leaf]
  unless prepared.size == 2 do throwError "native batch lost a lookup kind"
  let expected := #[known.lookup.leaf.type, target.leaf.type]
  for i in [:prepared.size] do
    let some entry := prepared[i]? | throwError "native batch lost an original lookup"
    unless entry.lookup.leaf.type == expected[i]! do throwError "native batch changed its lookup kind or order"
    let _ ← auditProof entry.proof entry.lookup.leaf.type
    kernelCheck `__nativeBatchLookup entry.lookup.leaf.type entry.proof

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
    checkLookup ``Packing.find entry polynomial
    let value ← mkAppM ``Packing.value #[entry]
    let packet ← NativePackets.storedSign codec ctx value #[context]
    let record ← checkedRecord (← operations.valueSignReader context codec ctx value (jsonExpr packet))
    checkBinding `__nativeStoredOperand (← mkAppM ``ValueSign.value #[record]) value
    checkLookup ``ValueSign.find record value
  let argument := mkConst ``generator
  let core ← operations.core
  let candidate ← mkAppM ``Element.inverseOperations #[core, argument]
  let entry ← factory.packing owner candidate
  let result ← mkAppM ``Packing.value #[entry]
  let packet ← NativePackets.inverse codec ctx context argument result #[context]
  let inverse ← checkedRecord (← operations.inverseReader context codec ctx argument entry (jsonExpr packet))
  checkBinding `__nativeInverseOriginal (← mkAppM ``Packing.Inverse.argument
    #[← mkAppM ``InverseFact.inverse #[inverse]]) argument
  checkLookup ``InverseFact.find inverse argument
  logInfo "cached record readers checked original generator and canonical-zero packings, stored operands and native inverse candidate with the ordinary kernel"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
#native_readers_probe

end Hex.RealClosure.Algebraic.KernelReplay.NativeReadersProbe
