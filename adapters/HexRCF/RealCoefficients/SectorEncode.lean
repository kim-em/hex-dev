/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellPacketRead
public import HexRCF.RealCoefficients.RowEncode
public section
namespace Hex.RCF.RealCoefficients.SectorEncode
open Hex Hex.RealClosure Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [Hashable E] [Hashable Ctx] {sign : E → Int} {binding : Ctx}
variable {roots : List (Descriptor E Ctx sign binding)} {cut : Fin (roots.length+1)}
variable {queries : List (DensePoly E)}

/-- Freeze one ordinary sector using the established six-field cell layout. -/
@[expose] def packet (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (data : CellPackets.Sector sign binding roots cut queries) : Codec.Json :=
  let left := if h : 0 < cut.val then RowEncode.packet value ctx (data.sector.left h) else .null
  let right := if h : cut.val < roots.length then RowEncode.packet value ctx (data.sector.right h) else .null
  .arr #[value.encode data.sector.point,left,right,
    Codec.descriptor value ctx data.row.root.raw,
    Codec.graph value ctx (Dag.encode data.row.root.evidence),
    RowEncode.packet value ctx data.row.signs]

/-- Finite coverage of every stored selected-sign row, including unreachable
graph entries. This is a condition on a partial reader, not global lawfulness. -/
@[expose] def RowCovered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    {root : Descriptor E Ctx sign binding} {qs : List (DensePoly E)}
    (row : SelectedSigns root qs) : Prop :=
  value.Covers (Algebraic.SignEvidence.coefficients root.raw (Algebraic.SignEvidence.ofSigns row)) ∧
  ctx.Covers (Algebraic.SignEvidence.contexts root.raw (Algebraic.SignEvidence.ofSigns row))

/-- Root-indexed form of the existing owner row round-trip law. Constructing
the erased context supplies no new mathematical or codec assumption. -/
theorem read_row (value : ValueCodec E) (ctx : ValueCodec Ctx)
    {root : Descriptor E Ctx sign binding} {qs : List (DensePoly E)}
    (row : SelectedSigns root qs) (covered : RowCovered value ctx row) :
    RowOperations.read value ctx sign binding root qs (RowEncode.packet value ctx row) = .ok row := by
  let context := Algebraic.Context.adjoin root (fun _ => false)
  have law (other : Descriptor E Ctx sign binding) (same : context.root = other)
      (signs : SelectedSigns other qs) (coverage : RowCovered value ctx signs) :
      RowOperations.read value ctx sign binding other qs (RowEncode.packet value ctx signs) =
        .ok signs := by
    cases same
    exact RowEncode.read_covered value ctx context qs signs coverage.1 coverage.2
  exact law root (Algebraic.Context.root_adjoin root (fun _ => false)) row covered

/-- Assemble all ordinary-sector parsing around the explicit descriptor
restoration boundary. Finite row coverage supplies every selected-sign read;
only restoration of the point descriptor remains an owner-level premise. -/
theorem read_of_descriptor (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (data : CellPackets.Sector sign binding roots cut queries)
    (point : value.decode (value.encode data.sector.point) = .ok data.sector.point)
    (left : ∀ h, RowCovered value ctx (data.sector.left h))
    (right : ∀ h, RowCovered value ctx (data.sector.right h))
    (row : RowCovered value ctx data.row.signs)
    (descriptor : Algebraic.RootReplay.readDescriptor value ctx sign binding
      (Codec.descriptor value ctx data.row.root.raw)
      (Codec.graph value ctx (Dag.encode data.row.root.evidence)) = .ok data.row.root) :
    CellPacketRead.read value ctx sign binding [] roots cut queries (packet value ctx data) =
      .ok data := by
  have rowRead := read_row value ctx data.row.signs row
  have leftRead (h : 0 < cut.val) := read_row value ctx (data.sector.left h) (left h)
  have rightRead (h : cut.val < roots.length) := read_row value ctx (data.sector.right h) (right h)
  rcases data with ⟨⟨sample, l, ls, r, rs⟩, ⟨root, bound, signs⟩⟩
  dsimp only at point descriptor rowRead leftRead rightRead
  simp only [List.get_eq_getElem] at leftRead rightRead
  by_cases positive : 0 < cut.val <;> by_cases bounded : cut.val < roots.length <;>
    simp [CellPacketRead.read, CellPacketRead.readUsing, packet, Codec.tuple, Codec.Json.getArr_arr,
      positive, bounded, point, descriptor, leftRead, rightRead, ls, rs, bound, rowRead,
      bind, Except.bind, pure, Except.pure]
  all_goals first | rfl | (funext h; contradiction) | (constructor <;> funext h <;> contradiction)

end Hex.RCF.RealCoefficients.SectorEncode
