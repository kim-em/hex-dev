/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexRealClosureMathlib.LocalSample
public meta import HexRealClosure.TowerContext

public section
namespace Hex.RCF.RealCoefficients.TowerSamples
open Hex Hex.RealClosure Hex.RealClosure.Tower

def registry : BaseContext.Registry := fun _ => none
abbrev base := Context.base (BaseContext.rational registry)

noncomputable def rational : Model base ℝ :=
  Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign

abbrev Selection := SignDet.Descriptor base.Value Signature base.sign base.signature
abbrev extension (d : Selection) := base.adjoin d
noncomputable def model (d : Selection) : Model (extension d).context ℝ := rational.adjoin d

/-- One source coefficient and one variable. The last atoms retain `(1, 2]`
as the shared strict-lower/non-strict-upper polynomial guards. -/
def schema : RealFormula.QF 2 :=
  let x : RealFormula.Poly 2 := MvPoly.X 1
  let q := x ^ 2 - MvPoly.X 0
  .and (.atom ⟨q, .eq⟩) (.and (.atom ⟨q ^ 2, .ge⟩)
    (.and (.atom ⟨1 - x, .lt⟩) (.atom ⟨x - 2, .le⟩)))

/-- Native root-finding receives actual shared-schema specialization, including
the repeated polynomial and both original domain guards. -/
def polynomials (d : Selection) : List (extension d).context.Poly :=
  RepresentationSpecialize.prepare (fun _ : Fin 1 => (extension d).generator) schema

def family (d : Selection) := Tower.Sample.family (extension d).context (polynomials d)

/-- Equal selected coefficients cancel the leading term only after substitution.
The zero atom and the half-open domain guards remain in the atom list. -/
def cancellation : RealFormula.QF 3 :=
  .and (.atom ⟨(MvPoly.X 0 - MvPoly.X 1) * MvPoly.X 2 ^ 4 + MvPoly.X 2 ^ 2, .ge⟩)
    (.and (.atom ⟨0, .eq⟩)
      (.and (.atom ⟨1 - MvPoly.X 2, .lt⟩) (.atom ⟨MvPoly.X 2 - 2, .le⟩)))

/-- The coefficient retains the exact real root of the original descriptor. -/
theorem selected (d : Selection) :
    (model d).value (extension d).generator =
      d.root rational.value rational.zero_iff rational.one rational.add rational.sub
        rational.mul rational.nat rational.sign := rational.adjoin_generator d

/-- Complete cell coverage and all signs use the same original real point. -/
theorem coverage (d : Selection) (x : ℝ) :
    ∃! region, region ∈ (family d).cells ∧ region.Mem (model d) x ∧
      region.sample.cell.contains region.sample.value = true ∧
      region.sample.signs (polynomials d) = (polynomials d).map (fun p => (SignType.sign
        ((HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff p).eval x) : Int)) := by
  obtain ⟨region, ⟨present, inside⟩, unique⟩ := (family d).cells_unique (model d) x
  obtain ⟨checked, signs⟩ := (family d).cell_signs (model d) region present
  refine ⟨region, ⟨present, inside, checked, signs x inside⟩, ?_⟩
  rintro other ⟨present, inside, _, _⟩
  exact unique other ⟨present, inside⟩

/-- One ordinary real sample realizes the entire computed sign vector together.
The actual coefficient conversion preserves the selected embedding. -/
theorem sector_real (d : Selection) (sample : Tower.Sample (extension d).context)
    (present : sample ∈ (family d).sectors) :
    ∃ realization : Conversion.Model sample.input (model d),
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      sample.signs (polynomials d) = (polynomials d).map (fun p => (SignType.sign
        ((HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff p).eval
          (realization.target.value sample.value)) : Int)) := by
  obtain ⟨realization, checked, signs⟩ := (family d).sector_signs (model d) sample present
  have inside := (Cell.contains_correct realization.target sample.cell sample.value).mp checked
  exact ⟨realization, inside, signs _ inside⟩

/-- The whole source atom traversal is evaluated at the same selected embedding. -/
theorem prepare_real (d : Selection) (x : ℝ) :
    (polynomials d).map (RepresentationSpecialize.evaluate (model d).value (model d).zero_iff x) =
      schema.polys.map (fun q => q.eval (RealFormula.append
        (fun _ : Fin 1 => (model d).value (extension d).generator) x)) :=
  RepresentationSpecialize.prepare_eval (model d).value (model d).zero_iff
    (model d).one (model d).add (model d).mul (model d).nat (model d).neg _ schema x

/-- Source-level coverage includes root sections and every ordinary real point. -/
theorem source_coverage (d : Selection) (x : ℝ) :
    ∃! region, region ∈ (family d).cells ∧ region.Mem (model d) x ∧
      region.sample.cell.contains region.sample.value = true ∧
      region.sample.signs (polynomials d) = schema.polys.map (fun q => (SignType.sign
        (q.eval (RealFormula.append
          (fun _ : Fin 1 => (model d).value (extension d).generator) x)) : Int)) := by
  obtain ⟨region, ⟨present, inside⟩, unique⟩ := (family d).cells_unique (model d) x
  obtain ⟨checked, signs⟩ := (family d).cell_signs (model d) region present
  refine ⟨region, ⟨present, inside, checked, ?_⟩, ?_⟩
  · rw [signs x inside]
    have values := congrArg (List.map (fun y : ℝ => (SignType.sign y : Int))) (prepare_real d x)
    simpa only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] using values
  · rintro other ⟨present, inside, _, _⟩
    exact unique other ⟨present, inside⟩

/-- Native specialization preserves semantic degrees after cancellation. -/
theorem degrees (d : Selection) :
    (polynomials d).map (fun q =>
      (HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff q).natDegree) =
      (polynomials d).map DensePoly.natDegree :=
  RepresentationSpecialize.prepare_degrees (model d).value (model d).zero_iff _ schema

/-- One ordinary real point satisfies every recorded source sign together,
including the original domain guards and repeated root condition. -/
theorem source_sector (d : Selection) (sample : Tower.Sample (extension d).context)
    (present : sample ∈ (family d).sectors) :
    ∃ realization : Conversion.Model sample.input (model d),
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      sample.signs (polynomials d) = schema.polys.map (fun q => (SignType.sign
        (q.eval (RealFormula.append
          (fun _ : Fin 1 => (model d).value (extension d).generator)
          (realization.target.value sample.value))) : Int)) := by
  obtain ⟨realization, inside, signs⟩ := sector_real d sample present
  refine ⟨realization, inside, ?_⟩
  rw [signs]
  have values := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (prepare_real d (realization.target.value sample.value))
  simpa only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] using values

/-- The original shared relation tags distinguish the open lower endpoint
from the closed upper endpoint. -/
def domain : RealFormula.QF 2 :=
  .and (.atom ⟨1 - MvPoly.X 1, .lt⟩) (.atom ⟨MvPoly.X 1 - 2, .le⟩)

/-- Use the existing strict shared Boolean fold on the recorded complete row. -/
def evaluateRow (row : List Int) (formula : RealFormula.QF 2) : Option Bool :=
  formula.evalSigns fun p =>
    ((schema.polys.zip row).find? (fun pair => pair.1 == p)).map
      (fun pair => Sign.ofInt pair.2)

/-- Execute the same native family over either selected real root of X²−2.
This is a computational regression, never proof evidence for a real goal. -/
def checked (lower upper : base.Value) (sections sectors : List (List Int))
    (sectionDomains sectorDomains sectionTruths : List (Option Bool)) : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some d := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C (1 + 1),
        lower := .finite lower, upper := .finite upper, indices := [], signs := [] }
    | return false
  let result := family d
  let samples := result.sections ++ result.sectors
  let cancelled := RepresentationSpecialize.prepare
    (fun _ : Fin 2 => (extension d).generator) cancellation
  let sectionRows := result.sections.map (fun sample => sample.signs (polynomials d))
  let sectorRows := result.sectors.map (fun sample => sample.signs (polynomials d))
  return (cancelled.map DensePoly.natDegree == [2, 0, 1, 1]) &&
    (cancelled[1]? == some 0) && result.boundaries.length == sections.length &&
    result.sections.length == sections.length && result.sectors.length == sections.length + 1 &&
    samples.all (fun sample => sample.cell.contains sample.value) &&
    sectionRows == sections && sectorRows == sectors &&
    sectionRows.map (fun row => evaluateRow row domain) == sectionDomains &&
    sectorRows.map (fun row => evaluateRow row domain) == sectorDomains &&
    sectionRows.map (fun row => evaluateRow row schema) == sectionTruths &&
    sectorRows.all (fun row => evaluateRow row schema == some false)

#guard checked 1 (1 + 1)
  [[0, 0, 1, -1], [-1, 1, 0, -1], [0, 0, -1, -1], [1, 1, -1, 0]]
  [[1, 1, 1, -1], [-1, 1, 1, -1], [-1, 1, -1, -1], [1, 1, -1, -1], [1, 1, -1, 1]]
  [some false, some false, some true, some true]
  [some false, some false, some true, some true, some false]
  [some false, some false, some true, some false]

-- The negative conjugate has no real root of X²−α; only guard boundaries remain.
#guard checked (-(1 + 1)) (-1)
  [[1, 1, 0, -1], [1, 1, -1, 0]]
  [[1, 1, 1, -1], [1, 1, -1, -1], [1, 1, -1, 1]]
  [some false, some true] [some false, some true, some false]
  [some false, some false]

end Hex.RCF.RealCoefficients.TowerSamples

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.coverage

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.sector_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.sector_real

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.selected

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.source_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.source_sector

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.prepare_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.prepare_real

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.degrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.degrees

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.source_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.source_coverage
