/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Data
import HexSignDet.Codec.Bytes
open Hex Hex.SignDet Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Emit
private unsafe def value (type : Type) (name : Name) : MetaM type := do
  evalExpr type (← inferType (mkConst name)) (mkConst name) (checkMeta := false)
private def graph (signs : SelectedSigns FiniteTower.first.root queries) : Codec.Json :=
  Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode signs.evidence)
/-- Round-trip the checked records and upper graphs through the owner codecs.
Only rational scalar graphs are regenerated. This does not independently
regenerate the packing inventory or the upper joint graphs. -/
private unsafe def emit : TermElabM Unit := do
  let facts ← value (List (SignFact FiniteTower.first)) ``Inputs.facts
  let entries ← value (List (Packing FiniteTower.first)) ``Packings.facts
  let records ← value (List (ValueSign FiniteTower.first)) ``Signs.facts
  let mut scalars := #[]
  let polynomials := facts.map SignFact.polynomial
  for polynomial in polynomials do
    let .ok (sign, proof) := FiniteTower.first.buildSignPacket ValueCodec.rat ValueCodec.nat polynomial
      | throwError "scalar production failed"
    scalars := scalars.push (Codec.Json.arr #[Codec.poly ValueCodec.rat polynomial, .number sign, proof])
  let mut packings := #[]
  for entry in entries do
    let .ok (sign, proof) := FiniteTower.first.buildSignPacket ValueCodec.rat ValueCodec.nat entry.representative
      | throwError "packing scalar production failed"
    packings := packings.push (Codec.Json.arr #[Codec.poly ValueCodec.rat entry.original,
      Codec.poly ValueCodec.rat entry.representative, .number sign, proof, graph entry.signs])
  let signs := records.toArray.map fun record =>
    Codec.Json.arr #[(Element.codec ValueCodec.rat).encode record.value, graph record.signs]
  let canonicalSigns ← value (SelectedSigns FiniteJoint.next.root
    (Schema.allQueries false Packings.facts)) ``Selected.canonical
  let guardedSigns ← value (SelectedSigns FiniteJoint.next.root
    (Schema.allQueries true Packings.facts)) ``Selected.guarded
  let canonical := (SignEvidence.codec (Element.codec ValueCodec.rat) ValueCodec.nat
    FiniteJoint.next.root.raw).encode ⟨Schema.allQueries false Packings.facts,
      canonicalSigns.values, Dag.encode canonicalSigns.evidence⟩
  let guarded := (SignEvidence.codec (Element.codec ValueCodec.rat) ValueCodec.nat
    FiniteJoint.next.root.raw).encode ⟨Schema.allQueries true Packings.facts,
      guardedSigns.values, Dag.encode guardedSigns.evidence⟩
  let packet := Codec.Json.arr #[canonical, guarded, Codec.Json.arr scalars, Codec.Json.arr packings, Codec.Json.arr signs]
  if let some path ← IO.getEnv "HEX_RCF_FINITE_MATRIX_OUTPUT" then
    IO.FS.writeBinFile path packet.writeBytes
  logInfo m!"frozen packet: scalar={polynomials.length}; packing={entries.length}; sign={records.length}"
@[implemented_by emit] private opaque runEmit : TermElabM Unit := pure ()
elab "#finite_packet_emit" : command => liftTermElabM runEmit
#finite_packet_emit
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Emit
