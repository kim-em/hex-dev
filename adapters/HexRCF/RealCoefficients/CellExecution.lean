/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellDecision
public section
namespace Hex.RCF.RealCoefficients
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet HexPolyTheory.Interpret

namespace CellBuild
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable [Hashable parent.Value] [Hashable Signature]

/-- The owner constructs the bound linear descriptor and complete source row. -/
theorem pointWith_success (model : Model parent ℝ) (point : parent.Value)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (queries : List parent.Poly) (same : queries = RepresentationSpecialize.prepare values formula) :
    ∃ packet, CellBuild.pointWith point values formula queries same = .ok packet := by
  subst queries
  obtain ⟨root, produced⟩ := CellProgress.point_descriptor model point
  obtain ⟨signs, signed⟩ := root.buildSigns_success model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv
    (RepresentationSpecialize.prepare values formula)
  have bound : (root.raw.head - Isolation.pointQuery point).isZero = true := by
    apply (sub_isZero model.value model.zero_iff model.sub _ _).mpr
    rw [Descriptor.build_raw produced]
  refine ⟨⟨root,bound,signs⟩, ?_⟩
  simp [CellBuild.pointWith, produced, Except.mapError, bound, signed, bind, Except.bind,
    pure, Except.pure]

/-- Standalone ordinary-point production succeeds through the same prepared helper. -/
theorem point_success (model : Model parent ℝ) (point : parent.Value)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) :
    ∃ packet, CellBuild.point point values formula = .ok packet := by
  simpa only [CellBuild.point] using pointWith_success model point values formula
    (RepresentationSpecialize.prepare values formula) rfl

/-- Open-cell membership makes every present strict boundary check succeed. -/
theorem bounds_success {p : DensePoly parent.Value} (model : Model parent ℝ)
    (roots : RootReplay.Result p .negInf .posInf) (cut : Fin (roots.roots.length+1))
    (point : parent.Value)
    (inside : Cell.Region (RootCells.points roots model) (.open cut) (model.value point)) :
    ∃ sector, bounds roots cut point = .ok sector := by
  by_cases positive : 0 < cut.val
  · obtain ⟨left, leftProduced, leftCode⟩ := BoundarySigns.left_sign model
      (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) point
      (CellProgress.left_bound roots model cut point inside positive)
    by_cases bounded : cut.val < roots.roots.length
    · obtain ⟨right, rightProduced, rightCode⟩ := BoundarySigns.right_sign model
        (roots.roots.get ⟨cut.val,bounded⟩) point
        (CellProgress.right_bound roots model cut point inside bounded)
      simp only [List.get_eq_getElem] at leftProduced rightProduced
      simp [bounds, positive, bounded, leftProduced, rightProduced, leftCode, rightCode,
        Except.mapError, bind, Except.bind, pure, Except.pure]
    · simp only [List.get_eq_getElem] at leftProduced
      simp [bounds, positive, bounded, leftProduced, leftCode,
        Except.mapError, bind, Except.bind, pure, Except.pure]
  · by_cases bounded : cut.val < roots.roots.length
    · obtain ⟨right, rightProduced, rightCode⟩ := BoundarySigns.right_sign model
        (roots.roots.get ⟨cut.val,bounded⟩) point
        (CellProgress.right_bound roots model cut point inside bounded)
      simp only [List.get_eq_getElem] at rightProduced
      simp [bounds, positive, bounded, rightProduced, rightCode,
        Except.mapError, bind, Except.bind, pure, Except.pure]
    · simp [bounds, positive, bounded, bind, Except.bind, pure, Except.pure]

/-- The executable typed producer succeeds on all sections and ordinary sectors. -/
theorem evidence_success {p : DensePoly parent.Value} (model : Model parent ℝ)
    (roots : RootReplay.Result p .negInf .posInf) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (points : Fin (roots.roots.length+1) → parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (inside : ∀ cut, Cell.Region (RootCells.points roots model) (.open cut) (model.value (points cut))) :
    ∃ data, evidence roots values guards formula points = .ok data := by
  let queries := RepresentationSpecialize.prepare values formula
  let sectionRead := fun i : Fin roots.roots.length =>
    (roots.roots.get i).buildSigns queries |>.mapError Error.production
  have sectionTotal (i : Fin roots.roots.length) : ∃ row, sectionRead i = .ok row := by
    obtain ⟨row, produced⟩ := (roots.roots.get i).buildSigns_success model.value model.zero_iff
      model.one model.add model.sub model.mul model.nat model.sign model.neg model.inv queries
    exact ⟨row, by simp only [sectionRead, produced, Except.mapError]⟩
  obtain ⟨sections, sectionDone, _⟩ := CellRead.collectWith_success Error.index
    (fun i => SelectedSigns (roots.roots.get i) queries) sectionRead sectionTotal
  let sector := fun cut : Fin (roots.roots.length+1) => do
    let bounds ← bounds roots cut (points cut)
    let row ← pointWith bounds.point values formula queries rfl
    pure (⟨bounds,row⟩ : SectorReplay.Result roots cut values formula)
  have sectorTotal (cut : Fin (roots.roots.length+1)) : ∃ row, sector cut = .ok row := by
    obtain ⟨bounds, boundsDone⟩ := bounds_success model roots cut (points cut) (inside cut)
    obtain ⟨row, rowDone⟩ := pointWith_success model bounds.point values formula queries rfl
    refine ⟨⟨bounds,row⟩, ?_⟩
    simp [sector, boundsDone, rowDone, bind, Except.bind, pure, Except.pure]
  obtain ⟨sectors, sectorDone, _⟩ := CellRead.collectWith_success Error.index
    (fun cut => SectorReplay.Result roots cut values formula) sector sectorTotal
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d present
    simpa only [decide_eq_true_eq] using guarded d present
  refine ⟨⟨sections,fun cut => (sectors cut).sector,fun cut => (sectors cut).row⟩, ?_⟩
  change (do
    unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw Error.divisor
    let sections ← CellRead.collectWith Error.index (fun i => SelectedSigns (roots.roots.get i) queries) sectionRead
    let sectors ← CellRead.collectWith Error.index (fun cut => SectorReplay.Result roots cut values formula) sector
    pure (⟨sections,fun cut => (sectors cut).sector,fun cut => (sectors cut).row⟩ :
      CellReplay.Evidence roots values formula)) = _
  simp only [all, ↓reduceIte, sectionDone, sectorDone,
    bind, Except.bind, pure, Except.pure]

/-- Every complete typed construction freezes successfully, retaining the
established literal layout. Finite-codec replay is a separate obligation. -/
theorem build_success {p : DensePoly parent.Value} (model : Model parent ℝ)
    (roots : RootReplay.Result p .negInf .posInf) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (points : Fin (roots.roots.length+1) → parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (inside : ∀ cut, Cell.Region (RootCells.points roots model) (.open cut) (model.value (points cut))) :
    ∃ literal, build roots values guards formula points = .ok literal := by
  obtain ⟨data, produced⟩ := evidence_success model roots values guards formula points guarded inside
  exact ⟨packet data, by simp only [build, produced, Functor.map, Except.map]⟩

end CellBuild

namespace CellDiscover
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- The public native discovery returns a complete frozen matrix whose actual
constructed typed rows give both exact original shared-sentence diagnostic verdicts.
This does not yet assert literal-reader or frontend quotation progress. -/
theorem run_success (original : Model parent ℝ) (values : Fin n → parent.Value)
    (guards : List parent.Value) (formula : RealFormula.QF (n+1))
    (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ packet, run values guards formula = .ok packet ∧
      let _ : Hashable packet.family.collection.input.context.Value :=
        RowEncode.hashable packet.family.collection.input.context.codec
      let _ : Hashable Signature := RowEncode.hashable Signature.codec
      ∃ candidates : Vector packet.family.collection.input.context.Value
          (packet.family.values.length+1),
        SectorRequest.points packet.family = some candidates ∧
      ∃ dimensions : packet.family.values.length+1 = packet.roots.roots.length+1,
      ∃ data : CellReplay.Evidence packet.roots
          (packet.family.collection.input.value ∘ values) formula,
        CellBuild.evidence packet.roots (packet.family.collection.input.value ∘ values)
          (guards.map packet.family.collection.input.value) formula
          (fun cut => candidates[Fin.cast dimensions.symm cut]) = .ok data ∧
        packet.cells = CellBuild.packet data ∧
        ∀ quantifier, ∃ verdict,
        CellReplay.check (packet.family.collection.input.value ∘ values) formula
          (guards.map packet.family.collection.input.value) packet.radical packet.roots
          data quantifier = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => original.value (values i))) := by
  classical
  let family := Tower.Sample.partition parent (RepresentationSpecialize.prepare values formula)
  let input := family.collection.input
  obtain ⟨model⟩ := family.model original
  have domains : ∀ d ∈ guards.map input.value, d ≠ 0 := by
    intro d member zero
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    apply guarded old present
    apply (original.zero_iff old).mp
    rw [← model.input.value old]
    exact (model.input.target.zero_iff _).mpr zero
  obtain ⟨prepared, produced, checked⟩ := CellBuild.prepare_success model.input.target
    (input.value ∘ values) (guards.map input.value) formula domains
  have aligned := CellAlignment.aligned values formula family original model prepared.1 prepared.2 checked
  have dimensions := CellAlignment.dimensions values formula family original model prepared.1 prepared.2 checked
  obtain ⟨candidates, requested, inside⟩ := CellAlignment.sector_vector family original model prepared.2 aligned
  let _ : Hashable input.context.Value := RowEncode.hashable input.context.codec
  let _ : Hashable Signature := RowEncode.hashable Signature.codec
  obtain ⟨data, built⟩ := CellBuild.evidence_success model.input.target prepared.2
    (input.value ∘ values) (guards.map input.value) formula
    (fun i => candidates[Fin.cast dimensions.symm i]) domains (inside dimensions)
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d present
    simpa only [decide_eq_true_eq] using guarded d present
  refine ⟨⟨family, prepared.1, prepared.2, CellBuild.packet data⟩, ?_,
    candidates, requested, dimensions, data, built, rfl, ?_⟩
  · unfold run
    simp only [all, ↓reduceIte]
    rw [produced, requested]
    cases prepared with
    | mk cert roots =>
      dsimp only at *
      rw [dite_eq_left dimensions]
      unfold CellBuild.build
      rw [built]
      rfl
  · intro quantifier
    obtain ⟨verdict, accepted, meaning⟩ := CellDecision.check_spec model.input.target
      (input.value ∘ values) formula (guards.map input.value) prepared.1 prepared.2 data
      quantifier domains checked
    refine ⟨verdict, accepted, ?_⟩
    have same : (fun i => model.input.target.value ((input.value ∘ values) i)) =
        (fun i => original.value (values i)) := funext (fun i => model.input.value (values i))
    simpa only [same] using meaning

end CellDiscover
end Hex.RCF.RealCoefficients
