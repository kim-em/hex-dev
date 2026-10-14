/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Ordinary
import HexSignDet.Codec.Bytes
open Hex Hex.SignDet Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Emit
private unsafe def value (type : Type) (name : Name) : MetaM type := do
  evalExpr type (← inferType (mkConst name)) (mkConst name) (checkMeta := false)
private unsafe def emit : TermElabM Unit := do
  let inverse ← value (Packing.Inverse.Equation Reader.entry) ``Records.inverse
  let alternate ← value (Packing.Inverse.Equation Reader.alternate) ``Records.alternate
  let entry ← value (Packing FiniteTower.first) ``Records.packing
  let .ok (sign, scalar) := FiniteTower.first.buildSignPacket ValueCodec.rat ValueCodec.nat entry.representative
    | throwError "quotient packing scalar round-trip failed"
  let packing := Codec.Json.arr #[Codec.poly ValueCodec.rat entry.original,
    Codec.poly ValueCodec.rat entry.representative, .number sign, scalar,
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode entry.signs.evidence)]
  let stale ← value Codec.Json ``Literals.staleGraph
  let packet := Codec.Json.arr #[
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode inverse.signs.evidence), packing,
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode alternate.signs.evidence), stale]
  if let some path ← IO.getEnv "HEX_RCF_QUOTIENT_OUTPUT" then
    IO.FS.writeBinFile path packet.writeBytes
  logInfo "two checked inverse graphs and one packing record round-tripped; stale field retained literally"
@[implemented_by emit] private opaque runEmit : TermElabM Unit := pure ()
elab "#frozen_quotient_emit" : command => liftTermElabM runEmit
#frozen_quotient_emit
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Emit
