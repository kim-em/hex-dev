/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellRead
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

variable [Hashable parent.Value] [Hashable Signature]

/-- Freeze an independently produced joint sign row with its exact descriptor. -/
@[expose] def row (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List (DensePoly parent.Value)) : Except Error Codec.Json := do
  let signs ← root.buildSigns queries |>.mapError Error.production
  return RowEncode.packet parent.codec Signature.codec signs

/-- Produce every section and ordinary-sector record for a supplied complete
root table. Ordinary points are proposals: strict adjacent signs are checked
before their records are retained. This does not construct predecessor scalar
inventories or discover points outside the parent field. -/
def build {p : DensePoly parent.Value}
    (roots : RootReplay.Result p .negInf .posInf) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (points : Fin (roots.roots.length+1) → parent.Value) : Except Error Codec.Json := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let queries := RepresentationSpecialize.prepare values formula
  let sections ← (List.finRange roots.roots.length).mapM fun i => row (roots.roots.get i) queries
  let sectors ← (List.finRange (roots.roots.length+1)).mapM fun cut => do
    let point := points cut
    let left ← if h : 0 < cut.val then do
      let root := roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩
      let signs ← root.buildSigns [Isolation.pointQuery point] |>.mapError Error.production
      unless signs.value == -1 do throw .boundary
      pure (RowEncode.packet parent.codec Signature.codec signs)
      else pure Codec.Json.Value.null
    let right ← if h : cut.val < roots.roots.length then do
      let root := roots.roots.get ⟨cut.val, h⟩
      let signs ← root.buildSigns [Isolation.pointQuery point] |>.mapError Error.production
      unless signs.value == 1 do throw .boundary
      pure (RowEncode.packet parent.codec Signature.codec signs)
      else pure Codec.Json.Value.null
    let raw : RawDescriptor parent.Value Signature :=
      ⟨parent.signature, Isolation.pointQuery point, .negInf, .posInf, [], []⟩
    let result ← Descriptor.build parent.sign parent.signature raw |>.mapError Error.production
    let root ← result.mapError Error.descriptor
    let signs ← row root queries
    return Codec.Json.arr #[parent.codec.encode point, left, right,
      Codec.descriptor parent.codec Signature.codec root.raw,
      Codec.graph parent.codec Signature.codec (Dag.encode root.evidence), signs]
  return .arr #[.arr sections.toArray, .arr sectors.toArray]
end Hex.RCF.RealCoefficients.CellBuild
