/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellCodec
public import HexRCF.RealCoefficients.RootCodec
public section
namespace Hex.RCF.RealCoefficients.CellFootprint
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E]
variable [Hashable E] [Hashable Ctx] {sign : E → Int} {binding : Ctx}

/-- All literal scalars in a selected row, using the owner's complete graph traversal. -/
@[expose] def rowValues {root : Descriptor E Ctx sign binding} {queries : List (DensePoly E)}
    (row : SelectedSigns root queries) : List E :=
  Algebraic.SignEvidence.coefficients root.raw (Algebraic.SignEvidence.ofSigns row)

/-- All literal context values in the same selected row. -/
@[expose] def rowContexts {root : Descriptor E Ctx sign binding} {queries : List (DensePoly E)}
    (row : SelectedSigns root queries) : List Ctx :=
  Algebraic.SignEvidence.contexts root.raw (Algebraic.SignEvidence.ofSigns row)

variable {roots : List (Descriptor E Ctx sign binding)} {cut : Fin (roots.length+1)}
variable {queries : List (DensePoly E)}

/-- Scalars stored by the six-field sector packet, retaining duplicates,
descriptor bounds and every encoded graph entry. No arithmetic is performed. -/
@[expose] def sectorValues (data : CellPackets.Sector sign binding roots cut queries) : List E :=
  [data.sector.point] ++
    (if h : 0 < cut.val then rowValues (data.sector.left h) else []) ++
    (if h : cut.val < roots.length then rowValues (data.sector.right h) else []) ++
    Codec.Coefficients.poly data.row.root.raw.head ++
    Codec.Coefficients.endpoint data.row.root.raw.lower ++
    Codec.Coefficients.endpoint data.row.root.raw.upper ++
    Codec.Coefficients.graph (Dag.encode data.row.root.evidence) ++ rowValues data.row.signs

/-- Contexts stored by both boundary rows, the point descriptor and its row. -/
@[expose] def sectorContexts (data : CellPackets.Sector sign binding roots cut queries) : List Ctx :=
  (if h : 0 < cut.val then rowContexts (data.sector.left h) else []) ++
    (if h : cut.val < roots.length then rowContexts (data.sector.right h) else []) ++
    [data.row.root.raw.context] ++ Codec.graphContexts (Dag.encode data.row.root.evidence) ++
    rowContexts data.row.signs

/-- A single finite inventory supplies every row and point premise around
descriptor restoration; no globally lawful coefficient reader is assumed. -/
theorem sector_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (data : CellPackets.Sector sign binding roots cut queries)
    (hv : value.Covers (sectorValues data)) (hc : ctx.Covers (sectorContexts data)) :
    value.decode (value.encode data.sector.point) = .ok data.sector.point ∧
    (∀ h, SectorEncode.RowCovered value ctx (data.sector.left h)) ∧
    (∀ h, SectorEncode.RowCovered value ctx (data.sector.right h)) ∧
    SectorEncode.RowCovered value ctx data.row.signs := by
  simp only [sectorValues, ValueCodec.covers_append, ValueCodec.covers_cons,
    ValueCodec.covers_nil, and_true] at hv
  simp only [sectorContexts, ValueCodec.covers_append, ValueCodec.covers_cons,
    ValueCodec.covers_nil, and_true] at hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hv.1.1.1.1.1.1.1
  · intro h
    have a := hv.1.1.1.1.1.1.2
    have b := hc.1.1.1.1
    simpa only [h, ↓reduceDIte, SectorEncode.RowCovered, rowValues, rowContexts] using And.intro a b
  · intro h
    have a := hv.1.1.1.1.1.2
    have b := hc.1.1.1.2
    simpa only [h, ↓reduceDIte, SectorEncode.RowCovered, rowValues, rowContexts] using And.intro a b
  · exact ⟨hv.2,hc.2⟩

/-- The same inventory retains every scalar and context of the separately
checked point descriptor, including all stored graph entries. -/
theorem descriptor_covered (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (data : CellPackets.Sector sign binding roots cut queries)
    (hv : value.Covers (sectorValues data)) (hc : ctx.Covers (sectorContexts data)) :
    value.Covers (Codec.Coefficients.poly data.row.root.raw.head) ∧
    value.Covers (Codec.Coefficients.endpoint data.row.root.raw.lower) ∧
    value.Covers (Codec.Coefficients.endpoint data.row.root.raw.upper) ∧
    value.Covers (Codec.Coefficients.graph (Dag.encode data.row.root.evidence)) ∧
    ctx.decode (ctx.encode data.row.root.raw.context) = .ok data.row.root.raw.context ∧
    ctx.Covers (Codec.graphContexts (Dag.encode data.row.root.evidence)) := by
  simp only [sectorValues, ValueCodec.covers_append] at hv
  simp only [sectorContexts, ValueCodec.covers_append, ValueCodec.covers_cons,
    ValueCodec.covers_nil, and_true] at hc
  exact ⟨hv.1.1.1.1.2,hv.1.1.1.2,hv.1.1.2,hv.1.2,hc.1.1.2,hc.1.2⟩

section Cells
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable [Hashable parent.Value] [Hashable Signature]
variable {p : DensePoly parent.Value} {table : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {formula : RealFormula.QF (n+1)}

/-- Every scalar serialized by the complete-cell payload. Original source
guards and reached arithmetic keys are separate inventories. -/
@[expose] def coefficients (data : CellReplay.Evidence table values formula) : List parent.Value :=
  (List.finRange table.roots.length).flatMap (fun i => rowValues (data.sections i)) ++
    (List.finRange (table.roots.length+1)).flatMap (fun cut => sectorValues (CellEncode.sector data cut))

/-- Every full context serialized by the same payload, in traversal order. -/
@[expose] def contexts (data : CellReplay.Evidence table values formula) : List Signature :=
  (List.finRange table.roots.length).flatMap (fun i => rowContexts (data.sections i)) ++
    (List.finRange (table.roots.length+1)).flatMap (fun cut => sectorContexts (CellEncode.sector data cut))

/-- Complete payload coverage supplies all section, sector and ordinary-point
reader premises. The inventory also retains point-descriptor graph literals. -/
theorem covered (value : ValueCodec parent.Value)
    (data : CellReplay.Evidence table values formula)
    (hv : value.Covers (coefficients data)) (hc : Signature.codec.Covers (contexts data)) :
    (∀ i, SectorEncode.RowCovered value Signature.codec (data.sections i)) ∧
    (∀ cut, value.decode (value.encode (data.sectors cut).point) = .ok (data.sectors cut).point) ∧
    (∀ cut h, SectorEncode.RowCovered value Signature.codec ((data.sectors cut).left h)) ∧
    (∀ cut h, SectorEncode.RowCovered value Signature.codec ((data.sectors cut).right h)) ∧
    (∀ cut, SectorEncode.RowCovered value Signature.codec (data.sectorRows cut).signs) := by
  simp only [coefficients, ValueCodec.covers_append, ValueCodec.covers_flatMap] at hv
  simp only [contexts, ValueCodec.covers_append, ValueCodec.covers_flatMap] at hc
  have sectors (cut : Fin (table.roots.length+1)) := sector_covered value Signature.codec
    (CellEncode.sector data cut) (hv.2 cut (List.mem_finRange cut))
      (hc.2 cut (List.mem_finRange cut))
  refine ⟨?_, fun cut => (sectors cut).1, fun cut => (sectors cut).2.1,
    fun cut => (sectors cut).2.2.1, fun cut => (sectors cut).2.2.2⟩
  intro i
  exact ⟨hv.1 i (List.mem_finRange i),hc.1 i (List.mem_finRange i)⟩

/-- The actual finite payload inventory suffices for the surrounding parser.
The owner signature codec supplies context roundtrips. Only descriptor
restoration and original guard validity remain explicit;
neither is inferred from literal coverage. -/
theorem read_covered (value : ValueCodec parent.Value)
    (data : CellReplay.Evidence table values formula) (guards : List parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (hv : value.Covers (coefficients data))
    (descriptors : ∀ cut, Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign parent.signature
      (Codec.descriptor value Signature.codec (data.sectorRows cut).root.raw)
      (Codec.graph value Signature.codec (Dag.encode (data.sectorRows cut).root.evidence)) =
        .ok (data.sectorRows cut).root) :
    CellRead.read value guards table values formula (CellEncode.packet value data) = .ok data := by
  obtain ⟨sections,points,left,right,rows⟩ := covered value data hv
    (Signature.codec_lawful.covers (contexts data))
  exact CellCodec.read_of_descriptors value data guards guarded sections points left right rows descriptors

/-- Finite coverage of the stored coefficient inventory is sufficient for
exact full-payload restoration. Point descriptors are restored by the actual
owner graph/binding laws, rather than supplied as reader-success premises. -/
theorem read_packet (value : ValueCodec parent.Value)
    (data : CellReplay.Evidence table values formula) (guards : List parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (hv : value.Covers (coefficients data)) :
    CellRead.read value guards table values formula (CellEncode.packet value data) = .ok data := by
  apply read_covered value data guards guarded hv
  intro cut
  have all := hv
  simp only [coefficients, ValueCodec.covers_append, ValueCodec.covers_flatMap] at all
  obtain ⟨head,lower,upper,graph,context,contexts⟩ := descriptor_covered value Signature.codec
    (CellEncode.sector data cut) (all.2 cut (List.mem_finRange cut))
    (Signature.codec_lawful.covers _)
  exact RootCodec.read_covered value Signature.codec (data.sectorRows cut).root
    head lower upper graph context contexts

end Cells
end Hex.RCF.RealCoefficients.CellFootprint
