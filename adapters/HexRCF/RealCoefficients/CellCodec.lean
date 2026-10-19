/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellEncode
public import HexRCF.RealCoefficients.SectorEncode
-- `packet_eq` unfolds the non-exposed writers `Codec.graph`, `Codec.node`
-- and the query-certificate encoders in `Codec.Evidence` to show that only
-- the encoder field is used. Public tuple/array laws alone do not prove this.
import all HexSignDet.Codec
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
public section
namespace Hex.RCF.RealCoefficients.CellCodec
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value} {roots : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {formula : RealFormula.QF (n+1)}

/-- Replacing only the coefficient decoder cannot change a frozen packet.
The actual encoding functions must agree; finite reader coverage alone would
not justify replaying the native writer's bytes. -/
theorem packet_eq [Hashable parent.Value] [Hashable Signature]
    (first second : ValueCodec parent.Value) (same : first.encode = second.encode)
    (data : CellReplay.Evidence roots values formula) :
    CellEncode.packet first data = CellEncode.packet second data := by
  cases first with
  | mk encode decode =>
    cases second with
    | mk other read =>
      dsimp only at same
      cases same
      rfl

/-- Exact arrays of finite indices retain their dimensions and order. -/
theorem tuple_fin (m : Nat) (f : Fin m → Codec.Json) :
    Codec.tuple m (.arr ((List.finRange m).map f).toArray) = .ok (Vector.ofFn f) := by
  rw [← List.ofFn_eq_map]
  simp [Codec.tuple, Codec.Json.getArr_arr, List.toArray_ofFn, Vector.ofFn,
    bind, Except.bind, pure, Except.pure]

/-- A strict dependent collection retains exactly the supplied successful
children. No index can be filled by a default value. -/
theorem collect_eq {ε : Type} {m : Nat} (failure : ε) (P : Fin m → Type)
    (read : (i : Fin m) → Except ε (P i)) (values : (i : Fin m) → P i)
    (accepted : ∀ i, read i = .ok (values i)) :
    CellRead.collectWith failure P read = .ok values := by
  obtain ⟨restored, done, children⟩ := CellRead.collectWith_success failure P read
    (fun i => ⟨values i, accepted i⟩)
  have same : restored = values := by
    funext i
    exact Except.ok.inj ((children i).symm.trans (accepted i))
  simpa only [same] using done

/-- Finite row coverage and descriptor restoration assemble the exact complete
cell reader result. `RootCodec.read_covered` supplies the descriptor restoration
for the higher-level finite-inventory theorem. Predecessor histories remain separate. -/
theorem read_of_descriptors [Hashable parent.Value] [Hashable Signature] (value : ValueCodec parent.Value)
    (data : CellReplay.Evidence roots values formula) (guards : List parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (sections : ∀ i, SectorEncode.RowCovered value Signature.codec (data.sections i))
    (points : ∀ cut, value.decode (value.encode (data.sectors cut).point) =
      .ok (data.sectors cut).point)
    (left : ∀ cut h, SectorEncode.RowCovered value Signature.codec ((data.sectors cut).left h))
    (right : ∀ cut h, SectorEncode.RowCovered value Signature.codec ((data.sectors cut).right h))
    (rows : ∀ cut, SectorEncode.RowCovered value Signature.codec (data.sectorRows cut).signs)
    (descriptors : ∀ cut, Algebraic.RootReplay.readDescriptor value Signature.codec parent.sign parent.signature
      (Codec.descriptor value Signature.codec (data.sectorRows cut).root.raw)
      (Codec.graph value Signature.codec (Dag.encode (data.sectorRows cut).root.evidence)) =
        .ok (data.sectorRows cut).root) :
    CellRead.read value guards roots values formula (CellEncode.packet value data) = .ok data := by
  have sectionRead (i : Fin roots.roots.length) :
      RowReplay.read value [] (roots.roots.get i) (RepresentationSpecialize.prepare values formula)
        (RowEncode.packet value Signature.codec (data.sections i)) = .ok (data.sections i) := by
    simpa only [RowReplay.read, List.all_nil, ↓reduceIte] using
      SectorEncode.read_row value Signature.codec (data.sections i) (sections i)
  have sectorRead (cut : Fin (roots.roots.length+1)) :
      SectorReplay.read value [] roots cut values formula
        (SectorEncode.packet value Signature.codec (CellEncode.sector data cut)) =
          .ok (⟨data.sectors cut, data.sectorRows cut⟩ : SectorReplay.Result roots cut values formula) := by
    have restored := SectorEncode.read_of_descriptor value Signature.codec (CellEncode.sector data cut)
      (points cut) (left cut) (right cut) (rows cut) (descriptors cut)
    simp only [SectorReplay.read, List.all_nil, ↓reduceIte, restored, bind, Except.bind,
      pure, Except.pure]
    rfl
  have sectionDone := collect_eq Replay.Error.binding _ _ data.sections sectionRead
  simp only [List.get_eq_getElem] at sectionDone
  have sectorDone := collect_eq Replay.Error.binding _ _
    (fun cut => (⟨data.sectors cut,data.sectorRows cut⟩ : SectorReplay.Result roots cut values formula)) sectorRead
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d member
    simpa only [decide_eq_true_eq] using guarded d member
  change CellRead.read value guards roots values formula
    (.arr #[.arr ((List.finRange roots.roots.length).map
      (fun i => RowEncode.packet value Signature.codec (data.sections i))).toArray,
      .arr ((List.finRange (roots.roots.length+1)).map
        (fun cut => SectorEncode.packet value Signature.codec (CellEncode.sector data cut))).toArray]) = _
  unfold CellRead.read
  simp only [all, ↓reduceIte]
  have outer (a b : Codec.Json) : Codec.tuple 2 (.arr #[a,b]) = .ok #v[a,b] := by
    simp [Codec.tuple, Codec.Json.getArr_arr, bind, Except.bind, pure, Except.pure]
  simp [outer, bind, Except.bind, tuple_fin, Vector.getElem_ofFn, Fin.getElem_fin,
    CellRead.collect, sectionDone, sectorDone, pure, Except.pure]

end Hex.RCF.RealCoefficients.CellCodec
