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

namespace CellRead
/-- Successful child calls produce the complete dependent family in index order. -/
theorem collectWith_success {ε : Type} {m : Nat} (failure : ε) (P : Fin m → Type)
    (read : (i : Fin m) → Except ε (P i))
    (total : ∀ i, ∃ value, read i = .ok value) :
    ∃ values, collectWith failure P read = .ok values := by
  classical
  choose values produced using total
  have same : (fun i => (do return ⟨i, ← read i⟩ : Except ε (Sigma P))) =
      (fun i => (pure ⟨i, values i⟩ : Except ε (Sigma P))) := by
    funext i
    simp [produced i, bind, Except.bind, pure, Except.pure]
  refine ⟨values, ?_⟩
  unfold collectWith
  rw [same, Vector.ofFnM_pure]
  simp only [bind, Except.bind, pure, Except.pure]
  have aligned : ∀ i : Fin m,
      (Vector.ofFn (fun i => (⟨i,values i⟩ : Sigma P)))[i].1 = i := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [dite_eq_left aligned]
  simp only [Except.ok.injEq]
  funext i
  have cast_entry (entry : Sigma P) (same : entry = ⟨i,values i⟩) (index : entry.1 = i) :
      index ▸ entry.2 = values i := by
    cases same
    rfl
  apply cast_entry
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]

end CellRead

namespace CellBuild
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable [Hashable parent.Value] [Hashable Signature]

/-- The owner constructs the bound linear descriptor and complete source row. -/
theorem point_success (model : Model parent ℝ) (point : parent.Value)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) :
    ∃ packet, CellBuild.point point values formula = .ok packet := by
  obtain ⟨root, produced⟩ := CellProgress.point_descriptor model point
  obtain ⟨signs, signed⟩ := root.buildSigns_success model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv
    (RepresentationSpecialize.prepare values formula)
  have bound : (root.raw.head - Isolation.pointQuery point).isZero = true := by
    apply (sub_isZero model.value model.zero_iff model.sub _ _).mpr
    rw [Descriptor.build_raw produced]
  refine ⟨⟨root,bound,signs⟩, ?_⟩
  simp [CellBuild.point, produced, Except.mapError, bound, signed, bind, Except.bind,
    pure, Except.pure]


omit [Hashable parent.Value] [Hashable Signature] in
/-- A root below the point produces the checked negative boundary sign. -/
theorem left_sign (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature) (point : parent.Value)
    (less : root.root model.value model.zero_iff model.one model.add model.sub model.mul model.nat model.sign
      < model.value point) :
    ∃ signs, root.buildSigns [Isolation.pointQuery point] = .ok signs ∧ signs.value = -1 := by
  obtain ⟨signs, produced⟩ := root.buildSigns_success model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv [Isolation.pointQuery point]
  refine ⟨signs, produced, ?_⟩
  rw [BoundarySigns.difference model root point signs]
  have observed := sign_eq_neg_one_iff.mpr (sub_neg.mpr less)
  rw [observed]
  rfl

omit [Hashable parent.Value] [Hashable Signature] in
/-- A root above the point produces the checked positive boundary sign. -/
theorem right_sign (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature) (point : parent.Value)
    (less : model.value point < root.root model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign) :
    ∃ signs, root.buildSigns [Isolation.pointQuery point] = .ok signs ∧ signs.value = 1 := by
  obtain ⟨signs, produced⟩ := root.buildSigns_success model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign model.neg model.inv [Isolation.pointQuery point]
  refine ⟨signs, produced, ?_⟩
  rw [BoundarySigns.difference model root point signs]
  have observed := sign_eq_one_iff.mpr (sub_pos.mpr less)
  rw [observed]
  rfl

/-- Open-cell membership makes every present strict boundary check succeed. -/
theorem bounds_success {p : DensePoly parent.Value} (model : Model parent ℝ)
    (roots : RootReplay.Result p .negInf .posInf) (cut : Fin (roots.roots.length+1))
    (point : parent.Value)
    (inside : Cell.Region (RootCells.points roots model) (.open cut) (model.value point)) :
    ∃ sector, bounds roots cut point = .ok sector := by
  by_cases positive : 0 < cut.val
  · obtain ⟨left, leftProduced, leftCode⟩ := left_sign model
      (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) point
      (CellProgress.left_bound roots model cut point inside positive)
    by_cases bounded : cut.val < roots.roots.length
    · obtain ⟨right, rightProduced, rightCode⟩ := right_sign model
        (roots.roots.get ⟨cut.val,bounded⟩) point
        (CellProgress.right_bound roots model cut point inside bounded)
      simp only [List.get_eq_getElem] at leftProduced rightProduced
      simp [bounds, positive, bounded, leftProduced, rightProduced, leftCode, rightCode,
        Except.mapError, bind, Except.bind, pure, Except.pure]
    · simp only [List.get_eq_getElem] at leftProduced
      simp [bounds, positive, bounded, leftProduced, leftCode,
        Except.mapError, bind, Except.bind, pure, Except.pure]
  · by_cases bounded : cut.val < roots.roots.length
    · obtain ⟨right, rightProduced, rightCode⟩ := right_sign model
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
  obtain ⟨sections, sectionDone⟩ := CellRead.collectWith_success Error.binding
    (fun i => SelectedSigns (roots.roots.get i) queries) sectionRead sectionTotal
  let sector := fun cut : Fin (roots.roots.length+1) => do
    let bounds ← bounds roots cut (points cut)
    let row ← point bounds.point values formula
    pure (⟨bounds,row⟩ : SectorReplay.Result roots cut values formula)
  have sectorTotal (cut : Fin (roots.roots.length+1)) : ∃ row, sector cut = .ok row := by
    obtain ⟨bounds, boundsDone⟩ := bounds_success model roots cut (points cut) (inside cut)
    obtain ⟨row, rowDone⟩ := point_success model bounds.point values formula
    refine ⟨⟨bounds,row⟩, ?_⟩
    simp [sector, boundsDone, rowDone, bind, Except.bind, pure, Except.pure]
  obtain ⟨sectors, sectorDone⟩ := CellRead.collectWith_success Error.binding
    (fun cut => SectorReplay.Result roots cut values formula) sector sectorTotal
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d present
    simpa only [decide_eq_true_eq] using guarded d present
  refine ⟨⟨sections,fun cut => (sectors cut).sector,fun cut => (sectors cut).row⟩, ?_⟩
  change (do
    unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw Error.divisor
    let sections ← CellRead.collectWith Error.binding (fun i => SelectedSigns (roots.roots.get i) queries) sectionRead
    let sectors ← CellRead.collectWith Error.binding (fun cut => SectorReplay.Result roots cut values formula) sector
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
      ∃ data : CellReplay.Evidence packet.roots
          (packet.family.collection.input.value ∘ values) formula,
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
  refine ⟨⟨family, prepared.1, prepared.2, CellBuild.packet data⟩, ?_, data, rfl, ?_⟩
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
