/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Sample

public section

namespace Hex.RealClosure.Tower.Sample.Tests

variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Ordinary imports suffice to apply the correctness theorem to an indexed result. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (index : Nat) (sample : Tower.Sample parent) (returned : family.sector? index = some sample) :
    ∃ realization : Conversion.Model sample.input original,
      HEq realization model.input ∧ sample.cell.contains sample.value = true := by
  obtain ⟨realization, aligned, checked, _, _⟩ :=
    family.sectors_correct original model sample (family.sector?_mem index sample returned)
  exact ⟨realization, aligned, checked⟩

/-- Cell coverage refers to an actual returned sample with the same input ownership. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original) (x : K) :
    ∃ sample ∈ family.sections ++ family.sectors,
      ∃ cell : Cell family.collection.input.context,
        sample.cellView = ⟨family.collection.input, cell⟩ ∧ cell.Mem model.input.target x := by
  obtain ⟨cell, ⟨member, inside⟩, _⟩ := family.cells_unique original model x
  have present : (⟨family.collection.input, cell⟩ : (input : Conversion parent) × Cell input.context) ∈
      family.cells.map (fun cell => ⟨family.collection.input, cell⟩) :=
    List.mem_map.mpr ⟨cell, member, rfl⟩
  rw [← family.cells_eq] at present
  obtain ⟨sample, member, equal⟩ := List.mem_map.mp present
  exact ⟨sample, member, cell, equal, inside⟩

/-- The named section API exposes its selected-root correctness under ordinary imports. -/
example (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (original : Model parent K) :
    ∃ _realization : Conversion.Model (Tower.Sample.section parent descriptor).input original,
      (Tower.Sample.section parent descriptor).cell.contains
        (Tower.Sample.section parent descriptor).value = true := by
  obtain ⟨realization, checked, _, _⟩ :=
    section_correct descriptor original
  exact ⟨realization, checked⟩

/-- Every actual adjacent cell can be requested using ordinary imports. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (lower upper : Endpoint family.collection.input.context.Value)
    (adjacent : Cell.sector lower upper ∈ family.cells) :
    ∃ sample, family.sectorBetween? lower upper = some sample :=
  family.sectorBetween?_success original model lower upper lower upper adjacent rfl rfl

/-- A root-free whole-line request succeeds without unfolding private definitions. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (empty : family.values = []) :
    ∃ sample, family.sectorBetween? .negInf .posInf = some sample :=
  family.sectorBetween?_success original model .negInf .posInf .negInf .posInf
    (family.wholeLine_mem empty) rfl rfl

/-- A caller may use any representative of the first boundary for its left ray. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (first upper : family.collection.input.context.Value)
    (rest : List family.collection.input.context.Value) (values : family.values = first :: rest)
    (same : model.input.target.value upper = model.input.target.value first) :
    ∃ sample, family.sectorBetween? .negInf (.finite upper) = some sample :=
  family.sectorBetween?_success original model .negInf (.finite upper) .negInf (.finite first)
    (family.leftRay_mem first rest values) rfl (congrArg Endpoint.finite same)

/-- The last boundary supplies an accepted right ray through ordinary imports. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (before : List family.collection.input.context.Value) (last lower : family.collection.input.context.Value)
    (values : family.values = before ++ [last])
    (same : model.input.target.value lower = model.input.target.value last) :
    ∃ sample, family.sectorBetween? (.finite lower) .posInf = some sample :=
  family.sectorBetween?_success original model (.finite lower) .posInf (.finite last) .posInf
    (family.rightRay_mem before last values) (congrArg Endpoint.finite same) rfl

/-- Consecutive list entries supply a bounded request without private unfolding. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (before after : List family.collection.input.context.Value)
    (a b lower upper : family.collection.input.context.Value)
    (values : family.values = before ++ a :: b :: after)
    (lowerSame : model.input.target.value lower = model.input.target.value a)
    (upperSame : model.input.target.value upper = model.input.target.value b) :
    ∃ sample, family.sectorBetween? (.finite lower) (.finite upper) = some sample :=
  family.sectorBetween?_success original model (.finite lower) (.finite upper) (.finite a) (.finite b)
    (family.bounded_mem before after a b values)
    (congrArg Endpoint.finite lowerSame) (congrArg Endpoint.finite upperSame)

/-- A boundary request provides its computed sign vector at every point of
the requested interval, using only the public checked result and ordinary imports. -/
example {polynomials : List parent.Poly} (family : Partition parent polynomials)
    (original : Model parent K) (model : Collection.Model family.collection original)
    (lower upper : Endpoint family.collection.input.context.Value) (sample : Tower.Sample parent)
    (returned : family.sectorBetween? lower upper = some sample) (x : K)
    (inside : (Cell.sector lower upper).Mem model.input.target x) :
    ∃ realization : Conversion.Model sample.input original,
      HEq realization model.input ∧ sample.signs polynomials = polynomials.map (fun p => (SignType.sign
        ((HexPolyMathlib.Interpret.interpret original.value original.zero_iff p).eval x) : Int)) := by
  obtain ⟨realization, aligned, _, interval⟩ :=
    family.sectorBetween?_correct original model lower upper sample returned
  obtain ⟨other, otherAligned, signs⟩ := family.sector_signs original model sample
    (family.sectorBetween?_mem lower upper sample returned)
  have same : other = realization := eq_of_heq (otherAligned.trans aligned.symm)
  subst other
  exact ⟨realization, aligned, signs x ((interval x).mpr inside)⟩

end Hex.RealClosure.Tower.Sample.Tests
