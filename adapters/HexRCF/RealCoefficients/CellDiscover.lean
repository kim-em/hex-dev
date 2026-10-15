/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SectorRequest
public import HexRealClosureTheory.Sample
public import HexSignDet.Codec.Bytes
public section
namespace Hex.RCF.RealCoefficients.CellDiscover
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

structure Packet (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) where
  family : Tower.Sample.Partition parent (RepresentationSpecialize.prepare values formula)
  radical : RadicalCert family.collection.input.context.Value Signature
  roots : @RootReplay.Result registry family.collection.input.context radical.core .negInf .posInf
  cells : Codec.Json

inductive Error where
  | divisor
  | preparation (cause : CellBuild.Error)
  | points
  | dimensions
  | cells (cause : CellBuild.Error)
  deriving Repr

/-- Native discovery through the owner's complete partition, followed by the
existing carrier/root/row producers after its actual coefficient conversion.
This retains native conversion history, not a frozen history certificate. -/
def run (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) : Except Error (Packet values guards formula) :=
  if guards.all (fun d => Decidable.decide (d ≠ 0)) then
    let family := Tower.Sample.partition parent (RepresentationSpecialize.prepare values formula)
    let input := family.collection.input
    let converted := input.value ∘ values
    let original := guards.map input.value
    match CellBuild.prepare (parent := input.context) converted original formula with
    | .error cause => .error (.preparation cause)
    | .ok ⟨radical, roots⟩ =>
      match SectorRequest.points family with
      | none => .error .points
      | some candidates =>
        if aligned : family.values.length+1 = roots.roots.length+1 then
          let _ : Hashable input.context.Value := RowEncode.hashable input.context.codec
          let _ : Hashable Signature := RowEncode.hashable Signature.codec
          match CellBuild.build roots converted original formula
              (fun i => candidates[Fin.cast aligned.symm i]) with
          | .error cause => .error (.cells cause)
          | .ok cells => .ok ⟨family, radical, roots, cells⟩
        else .error .dimensions
  else .error .divisor

/-- The owner's actual collection theorem supplies a compatible ordinary model
for the constructed common context. No model-conversion premise is assumed. -/
theorem Packet.model {values : Fin n → parent.Value} {guards : List parent.Value}
    {formula : RealFormula.QF (n+1)} (packet : Packet values guards formula)
    (original : Model parent ℝ) : Nonempty (Collection.Model packet.family.collection original) :=
  packet.family.model original

/-- Every fixed source coordinate keeps its original value in that same model. -/
theorem Packet.values {values : Fin n → parent.Value} {guards : List parent.Value}
    {formula : RealFormula.QF (n+1)} (packet : Packet values guards formula)
    (original : Model parent ℝ) (model : Collection.Model packet.family.collection original)
    (i : Fin n) :
    model.input.target.value (packet.family.collection.input.value (values i)) =
      original.value (values i) := model.input.value _

/-- Accepted complete cells in the common context prove the original shared
sentence at the original fixed coefficient values. The actual collection laws
supply the compatible target model and all source-coordinate equalities. -/
theorem Packet.sound {values : Fin n → parent.Value} {guards : List parent.Value}
    {formula : RealFormula.QF (n+1)} (packet : Packet values guards formula)
    (original : Model parent ℝ)
    (data : CellReplay.Evidence packet.roots
      (packet.family.collection.input.value ∘ values) formula)
    (quantifier : RealFormula.Quantifier)
    (accepted : CellReplay.check (packet.family.collection.input.value ∘ values) formula
      (guards.map packet.family.collection.input.value) packet.radical packet.roots data quantifier = .ok true) :
    (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
      (fun i => original.value (values i)) := by
  obtain ⟨model⟩ := packet.model original
  have truth := CellReplay.check_sound model.input.target _ formula _ packet.radical
    packet.roots data quantifier accepted
  have same : (fun i => model.input.target.value
      ((packet.family.collection.input.value ∘ values) i)) =
      (fun i => original.value (values i)) := funext (fun i => model.input.value (values i))
  simpa only [same] using truth

/-- Accepted replay retains each original supplied divisor at its original
source value, using a compatible model of the actual collection. -/
theorem Packet.domains {values : Fin n → parent.Value} {guards : List parent.Value}
    {formula : RealFormula.QF (n+1)} (packet : Packet values guards formula)
    (original : Model parent ℝ)
    (data : CellReplay.Evidence packet.roots
      (packet.family.collection.input.value ∘ values) formula)
    (quantifier : RealFormula.Quantifier) (verdict : Bool)
    (accepted : CellReplay.check (packet.family.collection.input.value ∘ values) formula
      (guards.map packet.family.collection.input.value) packet.radical packet.roots data quantifier = .ok verdict) :
    ∀ d ∈ guards, original.value d ≠ 0 := by
  obtain ⟨model⟩ := packet.model original
  have domains := CellReplay.check_domains model.input.target _ formula _ packet.radical
    packet.roots data quantifier verdict accepted
  intro d member
  have valid := domains (packet.family.collection.input.value d) (List.mem_map.mpr ⟨d, member, rfl⟩)
  simpa only [model.input.value] using valid

end Hex.RCF.RealCoefficients.CellDiscover
