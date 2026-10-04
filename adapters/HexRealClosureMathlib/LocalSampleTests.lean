/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.LocalSample

public section

namespace Hex.RealClosure.Tower.Sample
variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable {polynomials : List parent.Poly} (family : Family parent polynomials) (original : Model parent K)

example (x : K) : ∃! region, region ∈ family.cells ∧ region.Mem original x :=
  family.cells_unique original x

/-- Unique cell coverage and computed signs compose through the original model. -/
example (x : K) : ∃! region, region ∈ family.cells ∧ region.Mem original x ∧
    region.sample.cell.contains region.sample.value = true ∧
    region.sample.signs polynomials = polynomials.map (fun p => (SignType.sign
      ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  obtain ⟨region, ⟨present, inside⟩, unique⟩ := family.cells_unique original x
  obtain ⟨checked, signs⟩ := family.cell_signs original region present
  refine ⟨region, ⟨present, inside, checked, signs x inside⟩, ?_⟩
  rintro other ⟨present, inside, _, _⟩
  exact unique other ⟨present, inside⟩

example (upper : Root parent) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? .negInf (.finite upper) = some sample)
    (x : K) (inside : x < upper.denote original) :
    sample.signs polynomials = polynomials.map (fun p => (SignType.sign
      ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) :=
  family.sectorBetween?_signs original .negInf (.finite upper) sample returned x ⟨trivial, inside⟩

example (lower upper : Root parent) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? (.finite lower) (.finite upper) = some sample)
    (x : K) (left : lower.denote original < x) (right : x < upper.denote original) :
    sample.signs polynomials = polynomials.map (fun p => (SignType.sign
      ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) :=
  family.sectorBetween?_signs original (.finite lower) (.finite upper) sample returned x ⟨left, right⟩

example (root : Root parent) : (Region.section root).Ordered original := trivial

example (index : Nat) (region : Region parent) (selected : family.regions[index]? = some region)
    (sample : Tower.Sample parent) (returned : family.sector? index = some sample)
    (x : K) (inside : region.Mem original x) :
    sample.signs polynomials = polynomials.map (fun p => (SignType.sign
      ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  rw [family.sector?_eq, selected, Option.map_some, Option.some.injEq] at returned
  subst sample
  obtain ⟨realization, checked, cell, signs⟩ :=
    family.region_signs original region (List.mem_of_getElem? selected)
  exact signs x inside

example (root : Root parent) (member : root ∈ family.boundaries) :
    Region.section root ∈ family.cells ∧ (Region.section root).sample = Tower.Sample.ofRoot root :=
  ⟨(family.mem_cells _).mpr (Or.inl ⟨root, member, rfl⟩), Region.sample_section root⟩

example (before after : List (Root parent)) (a b : Root parent)
    (adjacent : family.boundaries = before ++ a :: b :: after) (x : K)
    (left : a.denote original < x) (right : x < b.denote original)
    (region : Region parent) (member : region ∈ family.cells) (inside : region.Mem original x) :
    region = Region.between a b := by
  obtain ⟨unique, present, only⟩ := family.cells_unique original x
  have bounded : Region.between a b ∈ family.cells :=
    (family.mem_cells _).mpr (Or.inr (family.bounded_mem before after a b adjacent))
  exact (only region ⟨member, inside⟩).trans (only (.between a b) ⟨bounded, left, right⟩).symm

example (sample : Tower.Sample parent) (present : sample ∈ family.sections) :
    ∃ root ∈ family.boundaries, sample = Tower.Sample.ofRoot root ∧
      sample.cell.contains sample.value = true ∧
      sample.signs polynomials = polynomials.map (fun p => (SignType.sign
        ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval
          (root.denote original)) : Int)) := family.sections_correct original sample present

example (sample : Tower.Sample parent) (present : sample ∈ family.sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.contains sample.value = true ∧ ∀ x, sample.cell.Mem realization.target x →
        sample.signs polynomials = polynomials.map (fun p => (SignType.sign
          ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) :=
  family.sector_signs original sample present

example (empty : family.boundaries = []) :
    ∃ sample, family.sectorBetween? .negInf .posInf = some sample :=
  family.sectorBetween?_success original .whole (family.wholeLine_mem empty)
    .negInf .posInf .negInf .posInf rfl rfl rfl

example (before after : List (Root parent)) (a b : Root parent)
    (adjacent : family.boundaries = before ++ a :: b :: after) :
    ∃ sample, family.sectorBetween? (.finite a) (.finite b) = some sample :=
  family.sectorBetween?_success original (.between a b) (family.bounded_mem before after a b adjacent)
    (.finite a) (.finite b) (.finite a) (.finite b) rfl rfl rfl

example (first : Root parent) (rest : List (Root parent))
    (boundary : family.boundaries = first :: rest) :
    ∃ sample, family.sectorBetween? .negInf (.finite first) = some sample :=
  family.sectorBetween?_success original (.left first) (family.leftRay_mem first rest boundary)
    .negInf (.finite first) .negInf (.finite first) rfl rfl rfl

example (before : List (Root parent)) (last : Root parent)
    (boundary : family.boundaries = before ++ [last]) :
    ∃ sample, family.sectorBetween? (.finite last) .posInf = some sample :=
  family.sectorBetween?_success original (.right last) (family.rightRay_mem before last boundary)
    (.finite last) .posInf (.finite last) .posInf rfl rfl rfl

end Hex.RealClosure.Tower.Sample
