/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Ordinary
import HexRCF.FiniteMatrix.Guards.Refusals
import HexSignDet.Codec.Bytes
open Hex Hex.SignDet Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Hex.RCF.RealCoefficients.FiniteMatrixTests
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Emit
private unsafe def value (type : Type) (name : Name) : MetaM type := do
  evalExpr type (← inferType (mkConst name)) (mkConst name) (checkMeta := false)
private unsafe def emit : TermElabM Unit := do
  let positive ← value (SelectedSigns FiniteJoint.next.root (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.allQueries false Packings.facts))
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.positive
  let zero ← value (SelectedSigns FiniteJoint.next.root (Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.allQueries true Packings.facts))
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.zero
  let extra ← value (ValueSign FiniteTower.first) ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Records.extra
  let codec := SignEvidence.codec (Element.codec ValueCodec.rat) ValueCodec.nat FiniteJoint.next.root.raw
  let positive := codec.encode ⟨Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.allQueries false Packings.facts,
    positive.values, Dag.encode positive.evidence⟩
  let zero := codec.encode ⟨Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Schema.allQueries true Packings.facts, zero.values, Dag.encode zero.evidence⟩
  let sign := Codec.Json.arr #[(Element.codec ValueCodec.rat).encode extra.value,
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode extra.signs.evidence)]
  let packet := Codec.Json.arr #[positive, zero, Codec.Json.arr #[], Codec.Json.arr #[], Codec.Json.arr #[sign]]
  if let some path ← IO.getEnv "HEX_RCF_FINITE_GUARDS_OUTPUT" then
    IO.FS.writeBinFile path packet.writeBytes
  logInfo "two guard packets and one stored-sign record round-tripped from checked data"
@[implemented_by emit] private opaque runEmit : TermElabM Unit := pure ()
elab "#frozen_guard_roundtrip" : command => liftTermElabM runEmit
#frozen_guard_roundtrip
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Emit
