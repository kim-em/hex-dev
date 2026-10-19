/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellBuild
public import HexSignDetTheory.SelectedProducer
public import HexSignDetTheory.RootProducer
public section
namespace Hex.RCF.RealCoefficients.CellProgress
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet HexPolyTheory.Interpret
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- The standalone frozen-row helper progresses through the actual selected-sign producer. -/
theorem row_success [Hashable parent.Value] [Hashable Signature] (model : Model parent ℝ)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List (DensePoly parent.Value)) :
    ∃ packet, CellBuild.row root queries = .ok packet := by
  obtain ⟨signs, produced⟩ := root.buildSigns_success model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv queries
  refine ⟨RowEncode.packet parent.codec Signature.codec signs, ?_⟩
  simp [CellBuild.row, produced, Except.mapError]

theorem point_polynomial (model : Model parent ℝ) (point : parent.Value) :
    interpret model.value model.zero_iff (Isolation.pointQuery point) =
      Polynomial.X - Polynomial.C (model.value point) := by
  apply Polynomial.funext
  intro x
  rw [Isolation.pointQuery_eval model.value model.zero_iff model.one model.sub]
  simp

/-- The actual descriptor producer succeeds on the linear head for an ordinary point. -/
theorem point_descriptor (model : Model parent ℝ) (point : parent.Value) :
    ∃ root : Descriptor parent.Value Signature parent.sign parent.signature,
      Descriptor.build parent.sign parent.signature
        ⟨parent.signature, Isolation.pointQuery point, .negInf, .posInf, [], []⟩ = .ok (.ok root) := by
  classical
  let raw : RawDescriptor parent.Value Signature :=
    ⟨parent.signature, Isolation.pointQuery point, .negInf, .posInf, [], []⟩
  apply (Descriptor.build_success_iff model.value model.zero_iff model.one model.add model.sub
    model.mul model.nat model.neg model.inv parent.sign model.sign parent.signature raw).mpr
  have polynomial := point_polynomial model point
  have degree : 0 < (Isolation.pointQuery point).natDegree := by
    rw [← natDegree_interpret model.value model.zero_iff, polynomial]
    simp
  have roots : HexRealRootsTheory.Tarski.rootsIn
      (interpret model.value model.zero_iff (Isolation.pointQuery point)) .negInf .posInf =
      {model.value point} := by
    ext x
    simp [HexRealRootsTheory.Tarski.mem_rootsIn, polynomial]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [raw, RawDescriptor.wellFormed, degree]
  · change HexSturmTheory.Domain model.value model.zero_iff (Isolation.pointQuery point) .negInf .posInf
    rw [HexSturmTheory.domain_iff, polynomial]
    exact ⟨Polynomial.X_sub_C_ne_zero _, (Polynomial.irreducible_X_sub_C _).squarefree,
      trivial, trivial, trivial⟩
  · simp [raw, RawDescriptor.queries, signsAt, Hex.Endpoint.map, roots]

/-- Descriptor and joint-sign construction supply a checked row at this exact point. -/
theorem point_packet (model : Model parent ℝ) (point : parent.Value)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1)) :
    Nonempty (PointRows.Packet point values formula) := by
  obtain ⟨root, produced⟩ := point_descriptor model point
  have source := Descriptor.build_raw produced
  obtain ⟨signs, _⟩ := root.buildSigns_success model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv
    (RepresentationSpecialize.prepare values formula)
  refine ⟨⟨root, ?_, signs⟩⟩
  apply (sub_isZero model.value model.zero_iff model.sub _ _).mpr
  rw [source]

variable {p : DensePoly parent.Value}

theorem left_bound (roots : RootReplay.Result p .negInf .posInf) (model : Model parent ℝ)
    (cut : Fin (roots.roots.length+1)) (point : parent.Value)
    (inside : Cell.Region (RootCells.points roots model) (.open cut) (model.value point))
    (positive : 0 < cut.val) :
    RootCells.points roots model ⟨cut.val-1, by have := cut.isLt; omega⟩ < model.value point := by
  have empty : roots.roots.length ≠ 0 := by have := cut.isLt; omega
  have first : cut.val ≠ 0 := by omega
  by_cases last : cut.val = roots.roots.length
  · simpa [Cell.Region, empty, first, last] using inside
  · simp [Cell.Region, empty, first, last] at inside
    exact inside.1

theorem right_bound (roots : RootReplay.Result p .negInf .posInf) (model : Model parent ℝ)
    (cut : Fin (roots.roots.length+1)) (point : parent.Value)
    (inside : Cell.Region (RootCells.points roots model) (.open cut) (model.value point))
    (bounded : cut.val < roots.roots.length) :
    model.value point < RootCells.points roots model ⟨cut.val,bounded⟩ := by
  have empty : roots.roots.length ≠ 0 := by omega
  by_cases first : cut.val = 0
  · simpa [Cell.Region, empty, first] using inside
  · have last : cut.val ≠ roots.roots.length := by omega
    simp [Cell.Region, empty, first, last] at inside
    exact inside.2

theorem sector (roots : RootReplay.Result p .negInf .posInf) (model : Model parent ℝ)
    (cut : Fin (roots.roots.length+1)) (point : parent.Value)
    (inside : Cell.Region (RootCells.points roots model) (.open cut) (model.value point)) :
    ∃ result : SectorSamples.Sector roots cut, result.point = point := by
  have left (positive : 0 < cut.val) : ∃ signs : SelectedSigns
      (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) [Isolation.pointQuery point],
      signs.value = -1 := by
    obtain ⟨signs, _, code⟩ := BoundarySigns.left_sign model
      (roots.roots.get ⟨cut.val-1, by have := cut.isLt; omega⟩) point
      (left_bound roots model cut point inside positive)
    exact ⟨signs, code⟩
  have right (bounded : cut.val < roots.roots.length) : ∃ signs : SelectedSigns
      (roots.roots.get ⟨cut.val,bounded⟩) [Isolation.pointQuery point], signs.value = 1 := by
    obtain ⟨signs, _, code⟩ := BoundarySigns.right_sign model
      (roots.roots.get ⟨cut.val,bounded⟩) point
      (right_bound roots model cut point inside bounded)
    exact ⟨signs, code⟩
  choose left leftSign using left
  choose right rightSign using right
  exact ⟨⟨point, left, leftSign, right, rightSign⟩, rfl⟩

/-- Assemble typed complete-cell evidence from points in their exact sectors.
Literal serialization and reader coverage are separate obligations. -/
theorem evidence (model : Model parent ℝ) (roots : RootReplay.Result p .negInf .posInf)
    (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (points : Fin (roots.roots.length+1) → parent.Value)
    (inside : ∀ cut, Cell.Region (RootCells.points roots model) (.open cut) (model.value (points cut))) :
    Nonempty (CellReplay.Evidence roots values formula) := by
  classical
  let sectors := fun cut => (sector roots model cut (points cut) (inside cut)).choose
  let rows := fun cut => Classical.choice (CellProgress.point_packet model (sectors cut).point values formula)
  have sections (i : Fin roots.roots.length) :=
    (roots.roots.get i).buildSigns_success model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign model.neg model.inv (RepresentationSpecialize.prepare values formula)
  exact ⟨⟨fun i => (sections i).choose, sectors, rows⟩⟩

end Hex.RCF.RealCoefficients.CellProgress
