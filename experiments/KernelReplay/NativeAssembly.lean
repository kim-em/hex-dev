/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTowerReal
public meta import KernelReplay.FiniteTowerReal
public meta import HexRealClosureMathlib.NativeAssembly
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
import all HexRealClosureMathlib.SignReplay
import all HexRealClosure.SignCodec

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyProbe
open FiniteTowerReal

/-- Correspondence for the actual native first-level inverse. -/
theorem read_inv (a : Element FiniteTower.first) : read a⁻¹ = (read a)⁻¹ :=
  Element.denote_inv ratCast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign
    cast_neg cast_inv (fun a b => Rat.cast_div a b) a

public meta section
open Lean Meta Elab Command Hex.SignDet FiniteData FiniteTower

syntax (name := nativeAssemblyProbe) "#native_assembly_probe" : command
@[command_elab nativeAssemblyProbe]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM do
  let first := mkConst ``FiniteTower.first
  let upper := mkConst ``FiniteTowerUse.next
  let rat := mkConst ``ValueCodec.rat
  let nat := mkConst ``ValueCodec.nat
  let coefficient ← mkAppM ``Element #[first]
  let codec ← mkAppOptM ``Element.codec (coefficient.getAppArgs.map some ++ #[some rat])
  let firstOwner : NativeOwner := ⟨first, rat, nat, mkConst ``reduction,
    mkConst ``reduction_eq, fun polynomial claimed packet =>
      mkAppM ``RationalRoot.readFact? #[first, polynomial, claimed, packet]⟩
  let upperReduction ← mkAppM ``Context.reduce #[upper]
  let upperOwner : NativeOwner := ⟨upper, codec, nat, upperReduction,
    ← mkEqRefl upperReduction, fun _ _ _ => throwError "ordinary upper reader is unused"⟩
  let factory : NativeFactory := ⟨#[firstOwner, upperOwner]⟩
  let assembly : NativeAssembly := { factory, read := fun index operations codec polynomial claimed packet => do
    if index == 0 then
      return ← mkAppM ``RationalRoot.readFact? #[first, polynomial, claimed, packet]
    unless index == 1 do throwError "fixture has no scalar model at this depth"
    let equality ← mkAppOptM ``Classical.decEq #[some (mkConst ``Real)]
    withLetDecl `realEquality (← inferType equality) equality fun inst => do
      let laws := #[mkConst ``FiniteTowerReal.read, mkConst ``read_zero, mkConst ``read_one,
        mkConst ``read_add, mkConst ``read_sub, mkConst ``read_mul, mkConst ``read_nat,
        mkConst ``read_sign, mkConst ``read_neg, mkConst ``read_inv]
      let reader ← mkAppM ``Context.readSignOperations?
        (laws ++ #[upper] ++ operations.operations ++ operations.equations ++
          #[operations.sign, operations.signEquation, codec, nat, polynomial, claimed, packet])
      return ← mkLetFVars #[inst] reader }
  let zero ← mkAppOptM ``Zero.zero #[some coefficient, none]
  let one ← mkAppOptM ``One.one #[some coefficient, none]
  let polynomial ← mkAppM ``DensePoly.ofCoeffs #[← mkArrayLit coefficient [zero, one]]
  let (claimed, packet) ← NativePackets.sign codec nat upper polynomial #[first, upper]
  let strict ← (← assembly.codecs).graph 1 packet
  let bounded := { assembly with fuel := 0 }
  let rejected ← try
    let _ ← bounded.complete 1 fun operations =>
      assembly.read 1 operations strict polynomial (toExpr claimed) (jsonExpr packet)
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith
        "native predecessor discovery did not finish" do throw error
    pure true
  unless rejected do throwError "native assembly accepted unsaturated predecessor inventories"
  let fact ← assembly.scalar 1 polynomial
  let tag ← mkAppM ``SignFact.sign #[fact]
  let equation ← mkEq tag (toExpr (1 : Int))
  let proof ← mkEqRefl (toExpr (1 : Int))
  let _ ← auditProof proof equation
  kernelCheck `__nativeAssemblyNestedSign equation proof
  logInfo "automatic predecessor collection independently checked the actual nested generator sign; exhausted discovery rejected"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
set_option trace.Hex.RealClosure.nativeAssembly true in
#native_assembly_probe

end
end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyProbe
