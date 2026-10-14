/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RepresentationCarrier
public import HexRCF.RealCoefficients.RootCells
public import HexRCF.RealCoefficients.Radical
public import HexRCF.RealCoefficients.Samples

public section
namespace Hex.RCF.RealCoefficients.RepresentationCells
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula HexPolyTheory.Interpret
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable (values : Fin n → parent.Value) (formula : QF (n+1))
variable (cert : RadicalCert parent.Value Signature)
variable (checked : cert.check parent.signature
  (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true)
variable (roots : RootReplay.Result cert.core .negInf .posInf) (model : Model parent ℝ)

include checked in
/-- Complete atom coverage is a conclusion of the checked radical identities
and the accepted full table, including zero and repeated atoms. -/
theorem atom_coverage (q : RealFormula.Poly (n+1)) (member : q ∈ formula.polys) :
    interpret model.value model.zero_iff (RepresentationSpecialize.polynomial values q) = 0 ∨
      ∀ x, (interpret model.value model.zero_iff
        (RepresentationSpecialize.polynomial values q)).IsRoot x →
        ∃ i, RootCells.points roots model i = x := by
  have present : RepresentationSpecialize.polynomial values q ∈
      RepresentationSpecialize.prepare values formula := List.mem_map.mpr ⟨q, member, rfl⟩
  rcases RepresentationCarrier.atom_roots model.value model.zero_iff model.one model.add model.mul
    _ _ present with zero | included
  · exact Or.inl zero
  · right
    intro x hx
    apply RootCells.complete roots model x
    apply (cert.roots model.value model.zero_iff model.one model.add model.sub model.mul
      parent.signature _ checked x).mpr
    exact included x hx

include checked in
/-- Source-atom signs are constant throughout each cell of the accepted table. -/
theorem sign_eq (q : RealFormula.Poly (n+1)) (member : q ∈ formula.polys)
    (cell : Cell roots.roots.length) {x y : ℝ}
    (hx : Cell.Region (RootCells.points roots model) cell x)
    (hy : Cell.Region (RootCells.points roots model) cell y) :
    SignType.sign (q.eval (append (fun i => model.value (values i)) x)) =
      SignType.sign (q.eval (append (fun i => model.value (values i)) y)) := by
  have constant := Cell.Region.sign_eq (RootCells.points roots model) (RootCells.ordered roots model)
    (interpret model.value model.zero_iff (RepresentationSpecialize.polynomial values q))
    (atom_coverage values formula cert checked roots model q member) cell hx hy
  simpa only [← RepresentationSpecialize.polynomial_eval model.value model.zero_iff model.one
    model.add model.mul model.nat model.neg values q,
    RepresentationSpecialize.evaluate] using constant

include checked in
/-- An exact row at one point remains exact everywhere in its checked cell. -/
theorem row_eq (cell : Cell roots.roots.length) (sample : ℝ)
    (inside : Cell.Region (RootCells.points roots model) cell sample)
    (row : List Int)
    (exactRow : row = formula.polys.map (fun q =>
      (SignType.sign (q.eval (append (fun i => model.value (values i)) sample)) : Int)))
    (x : ℝ) (hx : Cell.Region (RootCells.points roots model) cell x) :
    row = formula.polys.map (fun q =>
      (SignType.sign (q.eval (append (fun i => model.value (values i)) x)) : Int)) := by
  rw [exactRow]
  apply List.map_congr_left
  intro q member
  exact congrArg (fun s : SignType => (s : Int))
    (sign_eq values formula cert checked roots model q member cell inside hx)

include checked in
private theorem cell_eval
    (sample : Cell roots.roots.length → ℝ)
    (inside : ∀ c, Cell.Region (RootCells.points roots model) c (sample c))
    (rows : Cell roots.roots.length → List Int)
    (exactRows : ∀ c, rows c = formula.polys.map (fun q =>
      (SignType.sign (q.eval (append (fun i => model.value (values i)) (sample c))) : Int)))
    (c : Cell roots.roots.length) :
    ∃ value, Samples.Row.eval formula (rows c) = some value ∧
      ∀ x, Cell.Region (RootCells.points roots model) c x →
        (value = true ↔ formula.toProp (append (fun i => model.value (values i)) x)) := by
  obtain ⟨value, evaluated, _⟩ := Samples.Row.eval_spec formula (rows c)
    (append (fun i => model.value (values i)) (sample c)) (exactRows c)
  refine ⟨value, evaluated, ?_⟩
  intro x hx
  have exactRow := row_eq values formula cert checked roots model c (sample c)
    (inside c) (rows c) (exactRows c) x hx
  have semantic := Samples.Row.eval_true formula (rows c) _ exactRow
  simpa only [evaluated, Option.some.injEq] using semantic

include checked in
/-- Exact same-point rows supply the shared strict universal fold. Coverage
and sign constancy follow from the supplied table and checked identities. -/
theorem forall_rows
    (sample : Cell roots.roots.length → ℝ)
    (inside : ∀ c, Cell.Region (RootCells.points roots model) c (sample c))
    (rows : Cell roots.roots.length → List Int)
    (exactRows : ∀ c, rows c = formula.polys.map (fun q =>
      (SignType.sign (q.eval (append (fun i => model.value (values i)) (sample c))) : Int))) :
    OptionFold.allArray (Cell.all roots.roots.length)
      (fun c => Samples.Row.eval formula (rows c)) = some true ↔
      ∀ x : ℝ, formula.toProp (append (fun i => model.value (values i)) x) := by
  obtain ⟨verdict, evaluated, meaning⟩ := CellFold.Region.forall_spec
    (RootCells.points roots model) (RootCells.ordered roots model)
    (fun c => Samples.Row.eval formula (rows c))
    (fun x => formula.toProp (append (fun i => model.value (values i)) x))
    (cell_eval values formula cert checked roots model sample inside rows exactRows)
  simpa only [evaluated, Option.some.injEq] using meaning

include checked in
/-- The same checked cell partition supplies a strict existential fold, using
an ordinary real point for the entire row. -/
theorem exists_rows
    (sample : Cell roots.roots.length → ℝ)
    (inside : ∀ c, Cell.Region (RootCells.points roots model) c (sample c))
    (rows : Cell roots.roots.length → List Int)
    (exactRows : ∀ c, rows c = formula.polys.map (fun q =>
      (SignType.sign (q.eval (append (fun i => model.value (values i)) (sample c))) : Int))) :
    OptionFold.anyArray (Cell.all roots.roots.length)
      (fun c => Samples.Row.eval formula (rows c)) = some true ↔
      ∃ x : ℝ, formula.toProp (append (fun i => model.value (values i)) x) := by
  obtain ⟨verdict, evaluated, meaning⟩ := CellFold.Region.exists_spec
    (RootCells.points roots model) (RootCells.ordered roots model)
    (fun c => Samples.Row.eval formula (rows c))
    (fun x => formula.toProp (append (fun i => model.value (values i)) x))
    (cell_eval values formula cert checked roots model sample inside rows exactRows)
  simpa only [evaluated, Option.some.injEq] using meaning
end Hex.RCF.RealCoefficients.RepresentationCells
