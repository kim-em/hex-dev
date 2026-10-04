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

/-- Native root-finding receives every atom after shared-schema specialization. -/
def polynomials (d : Selection) (formula : RealFormula.QF (n + 1)) :
    List (extension d).context.Poly :=
  RepresentationSpecialize.prepare (fun _ : Fin n => (extension d).generator) formula

def family (d : Selection) (formula : RealFormula.QF (n + 1)) :=
  Tower.Sample.family (extension d).context (polynomials d formula)

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
theorem coverage (d : Selection) (formula : RealFormula.QF (n + 1)) (x : ℝ) :
    ∃! region, region ∈ (family d formula).cells ∧ region.Mem (model d) x ∧
      region.sample.cell.contains region.sample.value = true ∧
      region.sample.signs (polynomials d formula) = (polynomials d formula).map (fun p => (SignType.sign
        ((HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff p).eval x) : Int)) := by
  obtain ⟨region, ⟨present, inside⟩, unique⟩ := (family d formula).cells_unique (model d) x
  obtain ⟨checked, signs⟩ := (family d formula).cell_signs (model d) region present
  refine ⟨region, ⟨present, inside, checked, signs x inside⟩, ?_⟩
  rintro other ⟨present, inside, _, _⟩
  exact unique other ⟨present, inside⟩

/-- One ordinary real sample realizes the entire computed sign vector together.
The actual coefficient conversion preserves the selected embedding. -/
theorem sector_real (d : Selection) (formula : RealFormula.QF (n + 1)) (sample : Tower.Sample (extension d).context)
    (present : sample ∈ (family d formula).sectors) :
    ∃ realization : Conversion.Model sample.input (model d),
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      sample.signs (polynomials d formula) = (polynomials d formula).map (fun p => (SignType.sign
        ((HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff p).eval
          (realization.target.value sample.value)) : Int)) := by
  obtain ⟨realization, checked, signs⟩ := (family d formula).sector_signs (model d) sample present
  have inside := (Cell.contains_correct realization.target sample.cell sample.value).mp checked
  exact ⟨realization, inside, signs _ inside⟩

/-- The whole source atom traversal is evaluated at the same selected embedding. -/
theorem prepare_real (d : Selection) (formula : RealFormula.QF (n + 1)) (x : ℝ) :
    (polynomials d formula).map (RepresentationSpecialize.evaluate (model d).value (model d).zero_iff x) =
      formula.polys.map (fun q => q.eval (RealFormula.append
        (fun _ : Fin n => (model d).value (extension d).generator) x)) :=
  Samples.prepare_real (model d) (fun _ : Fin n => (extension d).generator) formula x

/-- Source-level coverage includes root sections and every ordinary real point. -/
theorem source_coverage (d : Selection) (formula : RealFormula.QF (n + 1)) (x : ℝ) :
    ∃! region, region ∈ (family d formula).cells ∧ region.Mem (model d) x ∧
      region.sample.cell.contains region.sample.value = true ∧
      region.sample.signs (polynomials d formula) = formula.polys.map (fun q => (SignType.sign
        (q.eval (RealFormula.append
          (fun _ : Fin n => (model d).value (extension d).generator) x)) : Int)) := by
  obtain ⟨region, ⟨present, inside⟩, unique⟩ := (family d formula).cells_unique (model d) x
  obtain ⟨checked, signs⟩ := (family d formula).cell_signs (model d) region present
  refine ⟨region, ⟨present, inside, checked, ?_⟩, ?_⟩
  · exact Samples.cell_signs (model d)
      (fun _ : Fin n => (extension d).generator) formula region present x inside
  · rintro other ⟨present, inside, _, _⟩
    exact unique other ⟨present, inside⟩

/-- Native specialization preserves semantic degrees after cancellation. -/
theorem degrees (d : Selection) (formula : RealFormula.QF (n + 1)) :
    (polynomials d formula).map (fun q =>
      (HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff q).natDegree) =
      (polynomials d formula).map DensePoly.natDegree :=
  RepresentationSpecialize.prepare_degrees (model d).value (model d).zero_iff _ formula

/-- The interpreted leading coefficient retains the same selected embedding. -/
theorem leading (d : Selection) (q : RealFormula.Poly (n + 1)) :
    (HexPolyMathlib.Interpret.interpret (model d).value (model d).zero_iff
      (RepresentationSpecialize.polynomial
        (fun _ : Fin n => (extension d).generator) q)).leadingCoeff =
      (model d).value (RepresentationSpecialize.polynomial
        (fun _ : Fin n => (extension d).generator) q).leadingCoeff := by
  exact RepresentationSpecialize.leading (model d).value (model d).zero_iff _ q

/-- One ordinary real point satisfies every recorded source sign together,
including the original domain guards and repeated root condition. -/
theorem source_sector (d : Selection) (formula : RealFormula.QF (n + 1)) (sample : Tower.Sample (extension d).context)
    (present : sample ∈ (family d formula).sectors) :
    ∃ realization : Conversion.Model sample.input (model d),
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      sample.signs (polynomials d formula) = formula.polys.map (fun q => (SignType.sign
        (q.eval (RealFormula.append
          (fun _ : Fin n => (model d).value (extension d).generator)
          (realization.target.value sample.value))) : Int)) := by
  exact Samples.sector_signs (model d)
    (fun _ : Fin n => (extension d).generator) formula sample present

/-- A section's selected boundary realizes the whole source sign vector at
one ordinary real point, including repeated atoms and domain guards. -/
theorem source_section (d : Selection) (formula : RealFormula.QF (n + 1))
    (sample : Tower.Sample (extension d).context)
    (present : sample ∈ (family d formula).sections) :
    ∃ root ∈ (family d formula).boundaries, sample = Tower.Sample.ofRoot root ∧
      sample.cell.contains sample.value = true ∧
      sample.signs (polynomials d formula) = formula.polys.map (fun q => (SignType.sign
        (q.eval (RealFormula.append
          (fun _ : Fin n => (model d).value (extension d).generator)
          (root.denote (model d)))) : Int)) := by
  exact Samples.section_signs (model d)
    (fun _ : Fin n => (extension d).generator) formula sample present

/-- On a lawful coefficient carrier, both specializations have exactly the
same real evaluation; stored-expression equality is not assumed. -/
theorem field_eval {D : Type u} [CommRing D] [DecidableEq D]
    (f : D →+* ℝ) (hz : ∀ a, f a = 0 ↔ a = 0)
    (values : Fin n → D) (q : RealFormula.Poly (n + 1)) (x : ℝ) :
    RepresentationSpecialize.evaluate f hz x (RepresentationSpecialize.polynomial values q) =
      FieldSpecialize.evaluate f x (FieldSpecialize.polynomial values q) := by
  have prepared := RepresentationSpecialize.polynomial_eval f hz f.map_one f.map_add f.map_mul
    (fun k => map_natCast f k) (fun a => map_neg f a) values q x
  exact prepared.trans (FieldSpecialize.polynomial_eval f values q x).symm

/-- The original shared relation tags distinguish the open lower endpoint
from the closed upper endpoint. -/
def domain (n : Nat) : RealFormula.QF (n + 1) :=
  .and (.atom ⟨1 - MvPoly.X (Fin.last n), .lt⟩)
    (.atom ⟨MvPoly.X (Fin.last n) - 2, .le⟩)

/-- Use the existing strict shared Boolean fold on the recorded complete row. -/
def evaluateRow (source : RealFormula.QF n) (row : List Int) (formula : RealFormula.QF n) : Option Bool :=
  formula.evalSigns fun p =>
    ((source.polys.zip row).find? (fun pair => pair.1 == p)).map
      (fun pair => Sign.ofInt pair.2)

/-- Execute the same native family over either selected real root of X²−2.
This is a computational regression, never proof evidence for a real goal. -/
def checked (formula : RealFormula.QF (n + 1)) (lower upper : base.Value) (sections sectors : List (List Int))
    (sectionDomains sectorDomains sectionTruths : List (Option Bool)) : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some d := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature, head := x * x - DensePoly.C (1 + 1),
        lower := .finite lower, upper := .finite upper, indices := [], signs := [] }
    | return false
  let result := family d formula
  let samples := result.sections ++ result.sectors
  let cancelled := RepresentationSpecialize.prepare
    (fun _ : Fin 2 => (extension d).generator) cancellation
  let sectionRows := result.sections.map (fun sample => sample.signs (polynomials d formula))
  let sectorRows := result.sectors.map (fun sample => sample.signs (polynomials d formula))
  return (cancelled.map DensePoly.natDegree == [2, 0, 1, 1]) &&
    (cancelled[1]? == some 0) && result.boundaries.length == sections.length &&
    result.sections.length == sections.length && result.sectors.length == sections.length + 1 &&
    samples.all (fun sample => sample.cell.contains sample.value) &&
    sectionRows == sections && sectorRows == sectors &&
    sectionRows.map (fun row => evaluateRow formula row (domain n)) == sectionDomains &&
    sectorRows.map (fun row => evaluateRow formula row (domain n)) == sectorDomains &&
    sectionRows.map (fun row => evaluateRow formula row formula) == sectionTruths &&
    sectorRows.all (fun row => evaluateRow formula row formula == some false)

#guard checked schema 1 (1 + 1)
  [[0, 0, 1, -1], [-1, 1, 0, -1], [0, 0, -1, -1], [1, 1, -1, 0]]
  [[1, 1, 1, -1], [-1, 1, 1, -1], [-1, 1, -1, -1], [1, 1, -1, -1], [1, 1, -1, 1]]
  [some false, some false, some true, some true]
  [some false, some false, some true, some true, some false]
  [some false, some false, some true, some false]

-- The negative conjugate has no real root of X²−α; only guard boundaries remain.
#guard checked schema (-(1 + 1)) (-1)
  [[1, 1, 0, -1], [1, 1, -1, 0]]
  [[1, 1, 1, -1], [1, 1, -1, -1], [1, 1, -1, 1]]
  [some false, some true] [some false, some true, some false]
  [some false, some false]

/-- The producer sees a repeated root, a literally duplicated atom, a zero
atom and a leading term cancelled by equal selected coefficient coordinates. -/
def mixed : RealFormula.QF 3 :=
  let q := MvPoly.X 2 ^ 2 - MvPoly.X 0
  .and (.atom ⟨q, .eq⟩) (.and (.atom ⟨q ^ 2, .ge⟩)
    (.and (.atom ⟨q, .eq⟩) cancellation))

-- The cancelled polynomial contributes the additional section at zero.
#guard checked mixed 1 (1 + 1)
  [[0, 0, 0, 1, 0, 1, -1], [-1, 1, -1, 0, 0, 1, -1],
    [-1, 1, -1, 1, 0, 0, -1], [0, 0, 0, 1, 0, -1, -1], [1, 1, 1, 1, 0, -1, 0]]
  [[1, 1, 1, 1, 0, 1, -1], [-1, 1, -1, 1, 0, 1, -1], [-1, 1, -1, 1, 0, 1, -1],
    [-1, 1, -1, 1, 0, -1, -1], [1, 1, 1, 1, 0, -1, -1], [1, 1, 1, 1, 0, -1, 1]]
  [some false, some false, some false, some true, some true]
  [some false, some false, some false, some true, some true, some false]
  [some false, some false, some false, some true, some false]

#guard checked mixed (-(1 + 1)) (-1)
  [[1, 1, 1, 0, 0, 1, -1], [1, 1, 1, 1, 0, 0, -1], [1, 1, 1, 1, 0, -1, 0]]
  [[1, 1, 1, 1, 0, 1, -1], [1, 1, 1, 1, 0, 1, -1],
    [1, 1, 1, 1, 0, -1, -1], [1, 1, 1, 1, 0, -1, 1]]
  [some false, some false, some true]
  [some false, some false, some true, some false]
  [some false, some false, some false]

/-- A reducible defining polynomial retains distinct nonzero representatives
of the selected value. Their difference still packs to the unique stored zero. -/
def noncanonicalCancellation : Bool := Id.run do
  let x : base.Poly := DensePoly.ofCoeffs #[0, 1]
  let some d := SignDet.Descriptor.validate base.sign base.signature
      { context := base.signature,
        head := (x * x - DensePoly.C (1 + 1)) * (x - DensePoly.C (1 + 1 + 1)),
        lower := .finite 1, upper := .finite (1 + 1), indices := [], signs := [] }
    | return false
  let g := (extension d).generator
  let h := g * g * g / (1 + 1)
  let values : Fin 2 → (extension d).context.Value := fun i => if i.val = 0 then g else h
  let prepared := RepresentationSpecialize.prepare values cancellation
  let result := Tower.Sample.family (extension d).context prepared
  return g != h && g - h == 0 &&
    prepared.map DensePoly.natDegree == [2, 0, 1, 1] &&
    result.boundaries.length == 3 &&
    result.sections.map (fun sample => sample.signs prepared) ==
      [[0, 0, 1, -1], [1, 0, 0, -1], [1, 0, -1, 0]] &&
    result.sectors.map (fun sample => sample.signs prepared) ==
      [[1, 0, 1, -1], [1, 0, 1, -1], [1, 0, -1, -1], [1, 0, -1, 1]]

#guard noncanonicalCancellation

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

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.source_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.source_section

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.leading

/-- info: 'Hex.RCF.RealCoefficients.TowerSamples.field_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.TowerSamples.field_eval
