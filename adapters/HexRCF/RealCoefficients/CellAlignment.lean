/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellDiscover
public import HexRCF.RealCoefficients.SectorRequest
public import Mathlib.Data.List.Sort
public section
namespace Hex.RCF.RealCoefficients.CellAlignment
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet HexPolyTheory.Interpret
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Exact root-union correspondence for the source atom carrier, omitting
only zero polynomial factors and retaining all repeated atom occurrences. -/
theorem product_roots (model : Model parent ℝ) (ps : List parent.Poly) (x : ℝ) :
    (interpret model.value model.zero_iff (RepresentationCarrier.product ps)).IsRoot x ↔
      ∃ p ∈ ps, p ≠ 0 ∧ (interpret model.value model.zero_iff p).IsRoot x := by
  induction ps with
  | nil => simp [RepresentationCarrier.product, interpret_one, model.one, Polynomial.IsRoot]
  | cons p ps ih =>
    by_cases zero : p = 0
    · subst p
      have expansion : RepresentationCarrier.product ((0 : parent.Poly)::ps) =
          RepresentationCarrier.product ps := by rfl
      rw [expansion]
      constructor
      · intro root
        obtain ⟨q, member, nz, root⟩ := ih.mp root
        exact ⟨q, List.mem_cons_of_mem _ member, nz, root⟩
      · rintro ⟨q, member, nz, root⟩
        apply ih.mpr
        rcases List.mem_cons.mp member with same | member
        · subst q
          exact False.elim (nz rfl)
        · exact ⟨q, member, nz, root⟩
    · have nonzero : p.isZero = false := by
        cases h : p.isZero with
        | false => rfl
        | true => exact False.elim (zero ((DensePoly.size_eq_zero_iff p).mp
            ((DensePoly.isZero_eq_true_iff p).mp h)))
      have expansion : RepresentationCarrier.product (p::ps) =
          p * RepresentationCarrier.product ps := by
        simp [RepresentationCarrier.product, nonzero]
      rw [expansion, interpret_mul model.value model.zero_iff model.add model.mul]
      simp only [Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero] at ih ⊢
      rw [ih]
      constructor
      · rintro (root | ⟨q, member, nz, root⟩)
        · exact ⟨p, List.mem_cons_self, zero, root⟩
        · exact ⟨q, List.mem_cons_of_mem _ member, nz, root⟩
      · rintro ⟨q, member, nz, root⟩
        rcases List.mem_cons.mp member with same | member
        · subst q
          exact Or.inl root
        · exact Or.inr ⟨q, member, nz, root⟩
theorem polynomial_eq (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (family : Tower.Sample.Partition parent (RepresentationSpecialize.prepare values formula))
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    (q : RealFormula.Poly (n+1)) :
    interpret model.input.target.value model.input.target.zero_iff
      (RepresentationSpecialize.polynomial (family.collection.input.value ∘ values) q) =
    interpret original.value original.zero_iff (RepresentationSpecialize.polynomial values q) := by
  apply Polynomial.funext
  intro x
  change RepresentationSpecialize.evaluate model.input.target.value model.input.target.zero_iff x _ =
    RepresentationSpecialize.evaluate original.value original.zero_iff x _
  rw [RepresentationSpecialize.polynomial_eval₂ model.input.target.value model.input.target.zero_iff
      model.input.target.one model.input.target.add model.input.target.mul model.input.target.nat
      model.input.target.neg,
    RepresentationSpecialize.polynomial_eval₂ original.value original.zero_iff original.one
      original.add original.mul original.nat original.neg]
  have same : (fun i => model.input.target.value ((family.collection.input.value ∘ values) i)) =
      (fun i => original.value (values i)) := funext (fun i => model.input.value (values i))
  rw [same]

theorem source_roots (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (family : Tower.Sample.Partition parent (RepresentationSpecialize.prepare values formula))
    (original : Model parent ℝ) (model : Collection.Model family.collection original) (x : ℝ) :
    (∃ p ∈ RepresentationSpecialize.prepare values formula,
      interpret original.value original.zero_iff p ≠ 0 ∧
        (interpret original.value original.zero_iff p).IsRoot x) ↔
    ∃ p ∈ RepresentationSpecialize.prepare (family.collection.input.value ∘ values) formula,
      p ≠ 0 ∧ (interpret model.input.target.value model.input.target.zero_iff p).IsRoot x := by
  constructor
  · rintro ⟨p, member, nonzero, root⟩
    obtain ⟨q, qmem, rfl⟩ := List.mem_map.mp member
    let converted := RepresentationSpecialize.polynomial (family.collection.input.value ∘ values) q
    have same := polynomial_eq values formula family original model q
    refine ⟨converted, List.mem_map.mpr ⟨q, qmem, rfl⟩, ?_, ?_⟩
    · intro zero
      apply nonzero
      rw [← same]
      change interpret model.input.target.value model.input.target.zero_iff converted = 0
      rw [zero, interpret_zero]
    · change (interpret model.input.target.value model.input.target.zero_iff
        (RepresentationSpecialize.polynomial (family.collection.input.value ∘ values) q)).IsRoot x
      rw [same]
      exact root
  · rintro ⟨p, member, nonzero, root⟩
    obtain ⟨q, qmem, rfl⟩ := List.mem_map.mp member
    have same := polynomial_eq values formula family original model q
    refine ⟨RepresentationSpecialize.polynomial values q, List.mem_map.mpr ⟨q, qmem, rfl⟩, ?_, ?_⟩
    · intro zero
      apply nonzero
      apply (interpret_eq_zero model.input.target.value model.input.target.zero_iff _).mp
      rw [same, zero]
    · rw [← same]
      exact root

/-- The owner partition and independently checked radical table have exactly
one common ordered real boundary list. No root-list equality is assumed. -/
theorem aligned (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (family : Tower.Sample.Partition parent (RepresentationSpecialize.prepare values formula))
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    (cert : RadicalCert family.collection.input.context.Value Signature)
    (roots : @RootReplay.Result registry family.collection.input.context cert.core .negInf .posInf)
    (checked : cert.check family.collection.input.context.signature
      (RepresentationCarrier.product
        (RepresentationSpecialize.prepare (family.collection.input.value ∘ values) formula)) = true) :
    family.values.map model.input.target.value = roots.values model.input.target := by
  apply List.Pairwise.eq_of_mem_iff
    (List.pairwise_map.mpr (family.sorted original model)) (roots.ordered model.input.target)
  intro x
  have table : x ∈ roots.values model.input.target ↔
      (interpret model.input.target.value model.input.target.zero_iff cert.core).IsRoot x := by
    rw [← (roots.coverage model.input.target).1 x]
    change x ∈ HexRealRootsTheory.Tarski.rootsIn
      (interpret model.input.target.value model.input.target.zero_iff cert.core) .negInf .posInf ↔ _
    rw [HexRealRootsTheory.Tarski.mem_rootsIn_iff _ (RootCells.nonzero roots model.input.target)]
    simp
  rw [family.coverage original model x, table,
    cert.roots model.input.target.value model.input.target.zero_iff model.input.target.one
      model.input.target.add model.input.target.sub model.input.target.mul
      family.collection.input.context.signature _ checked x,
    product_roots model.input.target]
  exact source_roots values formula family original model x

theorem dimensions (values : Fin n → parent.Value) (formula : RealFormula.QF (n+1))
    (family : Tower.Sample.Partition parent (RepresentationSpecialize.prepare values formula))
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    (cert : RadicalCert family.collection.input.context.Value Signature)
    (roots : @RootReplay.Result registry family.collection.input.context cert.core .negInf .posInf)
    (checked : cert.check family.collection.input.context.signature
      (RepresentationCarrier.product
        (RepresentationSpecialize.prepare (family.collection.input.value ∘ values) formula)) = true) :
    family.values.length+1 = roots.roots.length+1 := by
  have lengths := congrArg List.length (aligned values formula family original model cert roots checked)
  simp only [RootReplay.Result.values, List.length_map] at lengths
  exact congrArg (fun size => size+1) lengths

variable {polynomials : List parent.Poly}

theorem boundary (family : Tower.Sample.Partition parent polynomials)
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    {p : DensePoly family.collection.input.context.Value}
    (roots : @RootReplay.Result registry family.collection.input.context p .negInf .posInf)
    (aligned : family.values.map model.input.target.value = roots.values model.input.target)
    (i : Nat) (left : i < family.values.length) (right : i < roots.roots.length) :
    model.input.target.value family.values[i] = RootCells.points roots model.input.target ⟨i,right⟩ := by
  have same := congrArg (fun xs : List ℝ => xs[i]?) aligned
  simp only [RootReplay.Result.values, List.getElem?_map, List.getElem?_eq_getElem left,
    List.getElem?_eq_getElem right, Option.map_some, Option.some.injEq] at same
  exact same

theorem requested_inside (family : Tower.Sample.Partition parent polynomials)
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    {p : DensePoly family.collection.input.context.Value}
    (roots : @RootReplay.Result registry family.collection.input.context p .negInf .posInf)
    (aligned : family.values.map model.input.target.value = roots.values model.input.target)
    (cut : Fin (roots.roots.length+1))
    (point : family.collection.input.context.Value)
    (lengths : family.values.length = roots.roots.length)
    (member : (Tower.Cell.sector
      (SectorRequest.Cut.lower family (Fin.cast (congrArg (·+1) lengths.symm) cut))
      (SectorRequest.Cut.upper family (Fin.cast (congrArg (·+1) lengths.symm) cut))).Mem
        model.input.target (model.input.target.value point)) :
    Cell.Region (RootCells.points roots model.input.target) (.open cut) (model.input.target.value point) := by
  by_cases empty : roots.roots.length = 0
  · simp [Cell.Region, empty]
  · by_cases first : cut.val = 0
    · have present : 0 < family.values.length := by omega
      have right : 0 < roots.roots.length := by omega
      have upper := (boundary family original model roots aligned 0 present right)
      simp [SectorRequest.Cut.lower, SectorRequest.Cut.upper, Tower.Cell.Mem, first, present] at member
      simpa [Cell.Region, empty, first, ← upper] using member
    · have previous : cut.val-1 < family.values.length := by have := cut.isLt; omega
      have rootPrevious : cut.val-1 < roots.roots.length := by omega
      have lower := boundary family original model roots aligned (cut.val-1) previous rootPrevious
      by_cases last : cut.val = roots.roots.length
      · have final : ¬cut.val < family.values.length := by omega
        simp [SectorRequest.Cut.lower, SectorRequest.Cut.upper, Tower.Cell.Mem, first, final] at member
        have actual : RootCells.points roots model.input.target ⟨cut.val-1,rootPrevious⟩ <
            model.input.target.value point := by
          rw [← lower]
          exact member
        simpa [Cell.Region, empty, first, last] using actual
      · have bounded : cut.val < family.values.length := by have := cut.isLt; omega
        have rootBounded : cut.val < roots.roots.length := by omega
        have upper := boundary family original model roots aligned cut.val bounded rootBounded
        simp [SectorRequest.Cut.lower, SectorRequest.Cut.upper, Tower.Cell.Mem, first, bounded] at member
        simpa [Cell.Region, empty, first, last, ← lower, ← upper] using member

theorem sector_points (family : Tower.Sample.Partition parent polynomials)
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    {p : DensePoly family.collection.input.context.Value}
    (roots : @RootReplay.Result registry family.collection.input.context p .negInf .posInf)
    (aligned : family.values.map model.input.target.value = roots.values model.input.target) :
    ∃ points : Fin (roots.roots.length+1) → family.collection.input.context.Value,
      ∀ cut, Cell.Region (RootCells.points roots model.input.target) (.open cut)
        (model.input.target.value (points cut)) := by
  have lengths : family.values.length = roots.roots.length := by
    have same := congrArg List.length aligned
    simpa only [RootReplay.Result.values, List.length_map] using same
  obtain ⟨values, _, inside⟩ := SectorRequest.points_spec family original model
  refine ⟨fun cut => values (Fin.cast (congrArg (·+1) lengths.symm) cut), ?_⟩
  intro cut
  exact requested_inside family original model roots aligned cut _ lengths
    (inside (Fin.cast (congrArg (·+1) lengths.symm) cut))

end Hex.RCF.RealCoefficients.CellAlignment
