/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellEncode
public import HexRCF.RealCoefficients.RowEncode
public import HexRCF.RealCoefficients.RootBuild
public section
namespace Hex.RCF.RealCoefficients.CellBuild
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

inductive Error where
  | divisor
  | roots (error : RootBuild.Error)
  | production (error : BuildError)
  | descriptor (error : DescriptorError)
  | boundary
  | binding
  | index
  deriving Repr

/-- Original guard preflight precedes specialization, radical reduction and
complete root production. No source field or polynomial list is replaced. -/
def prepare (values : Fin n → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF (n+1)) :
    Except Error (Σ cert : RadicalCert parent.Value Signature,
      RootReplay.Result cert.core .negInf .posInf) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let input := RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)
  RootBuild.prepare input |>.mapError Error.roots

/-- The actual radical/root producers progress for any shared formula in a
lawful ordinary-real parent. Zero and repeated atoms need no nonzero-input
premise: the shared product omits exactly the zero factors. -/
theorem prepare_success (model : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ packet, prepare values guards formula = .ok packet ∧
      packet.1.check parent.signature
        (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true := by
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d member
    simpa only [decide_eq_true_eq] using guarded d member
  have nonzero := RepresentationCarrier.product_ne_zero model.value model.zero_iff
    model.one model.add model.mul (RepresentationSpecialize.prepare values formula)
  obtain ⟨packet, produced, checked⟩ := RootBuild.prepare_success model _ nonzero
  refine ⟨packet, ?_, checked⟩
  simp only [prepare, all, ↓reduceIte, produced, Except.mapError]

/-- Standalone helper freezing an independently produced joint sign row with its exact descriptor. -/
@[expose] def row [Hashable parent.Value] [Hashable Signature]
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List (DensePoly parent.Value)) : Except Error Codec.Json := do
  let signs ← root.buildSigns queries |>.mapError Error.production
  return RowEncode.packet parent.codec Signature.codec signs

/-- Construct a checked linear descriptor and complete source row at one
ordinary proposed point, retaining the literal head binding. -/
@[expose] def pointWith (value : parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) (queries : List parent.Poly)
    (same : queries = RepresentationSpecialize.prepare values formula) :
    Except Error (PointRows.Packet value values formula) := do
  let raw : RawDescriptor parent.Value Signature :=
    ⟨parent.signature, Isolation.pointQuery value, .negInf, .posInf, [], []⟩
  let result ← Descriptor.build parent.sign parent.signature raw |>.mapError Error.production
  let root ← result.mapError Error.descriptor
  if bound : (root.raw.head - Isolation.pointQuery value).isZero = true then
    let signs ← root.buildSigns queries |>.mapError Error.production
    return ⟨root,bound,same ▸ signs⟩
  else throw .binding

/-- Construct a standalone point row, preparing its source polynomials once. -/
@[expose] def point (value : parent.Value) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n+1)) : Except Error (PointRows.Packet value values formula) :=
  pointWith value values formula (RepresentationSpecialize.prepare values formula) rfl

/-- Check strict selected signs at every present adjacent boundary. -/
@[expose] def bounds {p : DensePoly parent.Value}
    (roots : RootReplay.Result p .negInf .posInf) (cut : Fin (roots.roots.length+1))
    (value : parent.Value) : Except Error (SectorSamples.Sector roots cut) := do
  let left : {f : (h : 0 < cut.val) → SelectedSigns
      (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) [Isolation.pointQuery value] //
      ∀ h, (f h).value = -1} ←
    if h : 0 < cut.val then do
      let signs ← (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩).buildSigns
        [Isolation.pointQuery value] |>.mapError Error.production
      if code : signs.value = -1 then pure ⟨fun _ => signs, fun _ => code⟩
      else throw .boundary
    else pure ⟨fun positive => False.elim (h positive), fun positive => False.elim (h positive)⟩
  let right : {f : (h : cut.val < roots.roots.length) → SelectedSigns
      (roots.roots.get ⟨cut.val,h⟩) [Isolation.pointQuery value] // ∀ h, (f h).value = 1} ←
    if h : cut.val < roots.roots.length then do
      let signs ← (roots.roots.get ⟨cut.val,h⟩).buildSigns
        [Isolation.pointQuery value] |>.mapError Error.production
      if code : signs.value = 1 then pure ⟨fun _ => signs, fun _ => code⟩
      else throw .boundary
    else pure ⟨fun bounded => False.elim (h bounded), fun bounded => False.elim (h bounded)⟩
  return ⟨value,left.1,left.2,right.1,right.2⟩

/-- Produce the complete typed matrix before serialization. All original
guards are preflighted before any section or sector work. -/
@[expose] def evidence {p : DensePoly parent.Value} (roots : RootReplay.Result p .negInf .posInf)
    (values : Fin n → parent.Value) (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (points : Fin (roots.roots.length+1) → parent.Value) :
    Except Error (CellReplay.Evidence roots values formula) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let queries := RepresentationSpecialize.prepare values formula
  let sections ← CellRead.collectWith Error.index (fun i => SelectedSigns (roots.roots.get i) queries)
    (fun i => (roots.roots.get i).buildSigns queries |>.mapError Error.production)
  let sectors ← CellRead.collectWith Error.index (fun cut => SectorReplay.Result roots cut values formula) (fun cut => do
    let sector ← bounds roots cut (points cut)
    let row ← pointWith sector.point values formula queries rfl
    return ⟨sector,row⟩)
  return ⟨sections,fun cut => (sectors cut).sector,fun cut => (sectors cut).row⟩

/-- Freeze all sections, strict boundaries and ordinary-point rows without
rerunning a root or selected-sign producer. -/
@[expose] def packet [Hashable parent.Value] [Hashable Signature]
    {p : DensePoly parent.Value} {roots : RootReplay.Result p .negInf .posInf}
    {values : Fin n → parent.Value} {formula : RealFormula.QF (n+1)}
    (data : CellReplay.Evidence roots values formula) : Codec.Json :=
  CellEncode.packet parent.codec data

/-- Produce and freeze complete cells at proposed ordinary points. The typed
producer retains every checked row; serialization preserves the established
packet layout. This does not construct predecessor scalar inventories. -/
@[expose] def build [Hashable parent.Value] [Hashable Signature] {p : DensePoly parent.Value}
    (roots : RootReplay.Result p .negInf .posInf) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (points : Fin (roots.roots.length+1) → parent.Value) : Except Error Codec.Json :=
  packet <$> evidence roots values guards formula points
end Hex.RCF.RealCoefficients.CellBuild
