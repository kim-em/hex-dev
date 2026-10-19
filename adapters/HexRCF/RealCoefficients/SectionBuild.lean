/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SectionReplay
public import HexSignDet.DagEncode

public section
namespace Hex.RCF.RealCoefficients.SectionBuild
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet

/-- Frozen output of a selected-section search. These are proposals, not proofs. -/
structure Packet where
  subject : Codec.Json
  graph : Codec.Json
  row : Codec.Json
  /-- Every stored predecessor coefficient in both graphs and the row, including
  duplicates and zeros. These are untrusted hints for strict-codec seed evidence. -/
  coefficients : List Codec.Json
  deriving Repr

/-- Producer failures retain the owner's actual error, independently of
invalid frozen replay. -/
inductive Error where
  | divisor
  | production (error : BuildError)
  | unresolved
  deriving Repr

/-- Search the native family for a true selected section and freeze its actual
descriptor and joint row. Point roots and sectors are outside this producer;
`none` means no supported witness was found, never a false existential verdict.
All guards are preflighted before root production. -/
def build {registry : BaseContext.Registry} (parent : Tower.Context registry)
    (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) : Except Error (Option Packet) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let required := RepresentationSpecialize.prepare values formula
  let family := Tower.Sample.family parent required
  let _ : Hashable parent.Value := ⟨fun a => hash (parent.codec.encode a)⟩
  let _ : Hashable Signature := ⟨fun a => hash (Signature.codec.encode a)⟩
  let mut found : Option Packet := none
  for boundary in family.boundaries do
    if found.isSome then continue
    match boundary with
    | .point _ => pure ()
    | .selected root _ _ =>
      let context := Algebraic.Context.adjoin root parent.isClean
      let packet ← match context.buildEvidence required with
        | .error error => throw (.production error)
        | .ok packet => pure packet
      match Samples.Row.eval formula packet.values.toList with
      | none => throw .unresolved
      | some false => pure ()
      | some true =>
        let rootGraph := Dag.encode root.evidence
        let coefficients := Codec.Coefficients.graph rootGraph ++
          Algebraic.SignEvidence.coefficients root.raw packet
        found := some {
          subject := Algebraic.SignRequests.binding parent.codec Signature.codec root.raw
          graph := Codec.graph parent.codec Signature.codec rootGraph
          row := (Algebraic.SignEvidence.codec parent.codec Signature.codec root.raw).encode packet
          coefficients := coefficients.map parent.codec.encode }
  return found

end Hex.RCF.RealCoefficients.SectionBuild
