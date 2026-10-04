/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Formula
public import HexRCF.RealCoefficients.RepresentationSpecialize
public import HexRCF.Soundness
public import HexRealClosureMathlib.LocalSample
public import HexRealRootsMathlib.RealClosed

public section

/-! Shared-formula truth for native ordinary-real cells and samples.
These are native producer APIs under an actual ordinary-real predecessor model,
not literal certificate replay, frontend source authentication or a general
joint realization theorem for symbolic infinitesimal contexts. -/

namespace Hex.RCF.RealCoefficients.Samples.Row
open Hex Hex.RealFormula

private theorem find_sign {A : Type} [BEq A] [LawfulBEq A]
    (keys : List A) (f : A → Int) (key : A) (member : key ∈ keys) :
    ((keys.zip (keys.map f)).find? (fun pair => pair.1 == key)).map
      (fun pair => Sign.ofInt pair.2) = some (Sign.ofInt (f key)) := by
  induction keys with
  | nil => simp at member
  | cons a keys ih =>
    by_cases same : a = key
    · subst key
      simp
    · have tail : key ∈ keys := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      simpa [List.find?_cons, same] using ih tail

/-- Evaluate only the supplied row through the shared Boolean evaluator.
A length mismatch is rejected; mathematical sign validity comes from the
actual cell laws, not from this low-level row evaluator. -/
@[expose] def eval (formula : RealFormula.QF n) (row : List Int) : Option Bool :=
  if row.length != formula.polys.length then none else
    formula.evalSigns fun p =>
      ((formula.polys.zip row).find? (fun pair => pair.1 == p)).map
        (fun pair => Sign.ofInt pair.2)

/-- Exact source signs make the existing strict Boolean traversal total and sound. -/
theorem eval_spec (formula : RealFormula.QF n) (row : List Int) (valuation : Fin n → ℝ)
    (exactRow : row = formula.polys.map (fun p => (SignType.sign (p.eval valuation) : Int))) :
    ∃ result, eval formula row = some result ∧ (result = true ↔ formula.toProp valuation) := by
  subst row
  simp only [eval, List.length_map, bne_self_eq_false, Bool.false_eq_true, ite_false]
  apply RealFormula.QF.evalSigns_spec
  intro p member
  refine ⟨Sign.ofInt (SignType.sign (p.eval valuation) : Int), find_sign _ _ _ member, ?_⟩
  rw [Sign.ofInt_spec]
  cases SignType.sign (p.eval valuation) <;> simp

/-- A true row is equivalent to the source proposition under its exact valuation. -/
theorem eval_true (formula : RealFormula.QF n) (row : List Int) (valuation : Fin n → ℝ)
    (exactRow : row = formula.polys.map (fun p => (SignType.sign (p.eval valuation) : Int))) :
    eval formula row = some true ↔ formula.toProp valuation := by
  obtain ⟨result, accepted, semantic⟩ := eval_spec formula row valuation exactRow
  simpa only [accepted, Option.some.injEq] using semantic

/-- Every authentic source row has a Boolean result, including false. -/
theorem eval_total (formula : RealFormula.QF n) (row : List Int) (valuation : Fin n → ℝ)
    (exactRow : row = formula.polys.map (fun p => (SignType.sign (p.eval valuation) : Int))) :
    ∃ result, eval formula row = some result := by
  obtain ⟨result, accepted, _⟩ := eval_spec formula row valuation exactRow
  exact ⟨result, accepted⟩

end Hex.RCF.RealCoefficients.Samples.Row

namespace Hex.RCF.RealCoefficients.Samples
open Hex Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Context registry}

/-- Prepare every source atom and construct the native root/cell family. -/
@[expose] def family (values : Fin n → parent.Value) (formula : RealFormula.QF (n + 1)) :=
  Tower.Sample.family parent (RepresentationSpecialize.prepare values formula)

/-- Append one bound real variable to the fixed coordinates interpreted by the supplied model. -/
@[expose] noncomputable def valuation (original : Model parent ℝ) (values : Fin n → parent.Value) (x : ℝ) :=
  RealFormula.append (fun i => original.value (values i)) x

/-- The complete ordered atom traversal agrees with the shared source valuation. -/
theorem prepare_real (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (x : ℝ) :
    (RepresentationSpecialize.prepare values formula).map
      (RepresentationSpecialize.evaluate original.value original.zero_iff x) =
      formula.polys.map (fun q => q.eval (valuation original values x)) :=
  RepresentationSpecialize.prepare_eval original.value original.zero_iff original.one original.add
    original.mul original.nat original.neg values formula x

/-- A selected boundary realizes the entire source sign vector at one real point. -/
theorem section_signs (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (sample : Tower.Sample parent)
    (present : sample ∈ (family values formula).sections) :
    ∃ root ∈ (family values formula).boundaries, sample = Tower.Sample.ofRoot root ∧
      sample.cell.contains sample.value = true ∧
      sample.signs (RepresentationSpecialize.prepare values formula) =
        formula.polys.map (fun q => (SignType.sign
          (q.eval (valuation original values (root.denote original))) : Int)) := by
  obtain ⟨root, member, same, checked, signs⟩ :=
    (family values formula).sections_correct original sample present
  refine ⟨root, member, same, checked, ?_⟩
  rw [signs]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (prepare_real original values formula (root.denote original))
  simpa only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] using evaluations

/-- The shared Boolean result at a section has the original source meaning. -/
theorem section_formula (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (sample : Tower.Sample parent)
    (present : sample ∈ (family values formula).sections) :
    ∃ root ∈ (family values formula).boundaries, sample = Tower.Sample.ofRoot root ∧
      (Row.eval formula
        (sample.signs (RepresentationSpecialize.prepare values formula)) = some true ↔
        formula.toProp (valuation original values (root.denote original))) := by
  obtain ⟨root, member, same, _, signs⟩ := section_signs original values formula sample present
  exact ⟨root, member, same, Row.eval_true _ _ _ signs⟩

/-- One compatible ordinary-real sample realizes all source signs together. -/
theorem sector_signs (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (sample : Tower.Sample parent)
    (present : sample ∈ (family values formula).sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      sample.signs (RepresentationSpecialize.prepare values formula) =
        formula.polys.map (fun q => (SignType.sign
          (q.eval (valuation original values (realization.target.value sample.value))) : Int)) := by
  obtain ⟨realization, checked, signs⟩ :=
    (family values formula).sector_signs original sample present
  have inside := (Cell.contains_correct realization.target _ _).mp checked
  refine ⟨realization, inside, ?_⟩
  rw [signs _ inside]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (prepare_real original values formula (realization.target.value sample.value))
  simpa only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] using evaluations

/-- The whole Boolean source formula is interpreted at the same real sector sample. -/
theorem sector_formula (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (sample : Tower.Sample parent)
    (present : sample ∈ (family values formula).sectors) :
    ∃ realization : Conversion.Model sample.input original,
      sample.cell.Mem realization.target (realization.target.value sample.value) ∧
      (Row.eval formula
        (sample.signs (RepresentationSpecialize.prepare values formula)) = some true ↔
        formula.toProp (valuation original values (realization.target.value sample.value))) := by
  obtain ⟨realization, inside, signs⟩ := sector_signs original values formula sample present
  exact ⟨realization, inside, Row.eval_true _ _ _ signs⟩

/-- Every point in a native cell has the complete recorded source sign vector. -/
theorem cell_signs (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (region : Tower.Sample.Region parent)
    (present : region ∈ (family values formula).cells) (x : ℝ)
    (inside : region.Mem original x) :
    region.sample.signs (RepresentationSpecialize.prepare values formula) =
      formula.polys.map (fun q => (SignType.sign (q.eval (valuation original values x)) : Int)) := by
  have signs := ((family values formula).cell_signs original region present).2 x inside
  rw [signs]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (prepare_real original values formula x)
  simpa only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] using evaluations

/-- The row result has the source meaning throughout its native cell. -/
theorem cell_formula (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (region : Tower.Sample.Region parent)
    (present : region ∈ (family values formula).cells) (x : ℝ)
    (inside : region.Mem original x) :
    Row.eval formula
      (region.sample.signs (RepresentationSpecialize.prepare values formula)) = some true ↔
      formula.toProp (valuation original values x) :=
  Row.eval_true _ _ _ (cell_signs original values formula region present x inside)

/-- Every actual native cell contains an ordinary real point. -/
theorem cell_real (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (region : Tower.Sample.Region parent)
    (present : region ∈ (family values formula).cells) : ∃ x : ℝ, region.Mem original x := by
  rcases ((family values formula).mem_cells region).mp present with sectionMember | sectorMember
  · obtain ⟨root, _, rfl⟩ := sectionMember
    exact ⟨root.denote original, rfl⟩
  · obtain ⟨realization, checked, cell, _⟩ :=
      (family values formula).region_signs original region sectorMember
    exact ⟨realization.target.value region.sample.value,
      (cell _).mp ((Cell.contains_correct realization.target _ _).mp checked)⟩

/-- Actual cell rows yield a Boolean, including a diagnostic false result. -/
theorem cell_total (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (region : Tower.Sample.Region parent)
    (present : region ∈ (family values formula).cells) :
    ∃ value, Row.eval formula
      (region.sample.signs (RepresentationSpecialize.prepare values formula)) = some value := by
  obtain ⟨x, inside⟩ := cell_real original values formula region present
  exact Row.eval_total _ _ _ (cell_signs original values formula region present x inside)

/-- Run native polynomial preparation, root/cell production and strict truth
folding. The Boolean is diagnostic production output, not a frozen replay
certificate or ordinary-kernel quotation evidence. All coordinates belong
to one parent context; independent fields need prior proved conversion. -/
@[expose] def run (values : Fin n → parent.Value) (formula : RealFormula.QF (n + 1))
    (quantifier : RealFormula.Quantifier) : Option Bool :=
  let prepared := RepresentationSpecialize.prepare values formula
  let cells := (Tower.Sample.family parent prepared).cells
  let evaluate := fun region : Tower.Sample.Region parent =>
    Row.eval formula (region.sample.signs prepared)
  match quantifier with
  | .forallReal => OptionFold.all evaluate cells
  | .existsReal => OptionFold.any evaluate cells

private theorem forall_run (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) :
    ∃ result, run values formula .forallReal = some result ∧
      (result = true ↔ ∀ x : ℝ, formula.toProp (valuation original values x)) := by
  obtain ⟨result, accepted, semantic⟩ := OptionFold.all_spec
    (cell_total original values formula)
  refine ⟨result, accepted, semantic.trans ?_⟩
  constructor
  · intro all x
    obtain ⟨region, ⟨member, inside⟩, _⟩ := (family values formula).cells_unique original x
    exact (cell_formula original values formula region member x inside).mp (all region member)
  · intro all region member
    obtain ⟨x, inside⟩ := cell_real original values formula region member
    exact (cell_formula original values formula region member x inside).mpr (all x)

private theorem exists_run (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) :
    ∃ result, run values formula .existsReal = some result ∧
      (result = true ↔ ∃ x : ℝ, formula.toProp (valuation original values x)) := by
  obtain ⟨result, accepted, semantic⟩ := OptionFold.any_spec
    (cell_total original values formula)
  refine ⟨result, accepted, semantic.trans ?_⟩
  constructor
  · rintro ⟨region, member, truth⟩
    obtain ⟨x, inside⟩ := cell_real original values formula region member
    exact ⟨x, (cell_formula original values formula region member x inside).mp truth⟩
  · rintro ⟨x, truth⟩
    obtain ⟨region, ⟨member, inside⟩, _⟩ := (family values formula).cells_unique original x
    exact ⟨region, member, (cell_formula original values formula region member x inside).mpr truth⟩

end Hex.RCF.RealCoefficients.Samples

namespace Hex.RCF.RealCoefficients.Samples
open Hex Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Context registry}

/-- Native region folds implement exactly the existing shared one-quantifier
semantics. Source coefficient identities and all original divisor guards
must still be authenticated by the frontend before source-goal quotation. -/
theorem run_spec (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, run values formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => original.value (values i))) := by
  cases quantifier with
  | forallReal =>
    simpa only [RealFormula.Prenex.toProp, valuation] using forall_run original values formula
  | existsReal =>
    simpa only [RealFormula.Prenex.toProp, valuation] using exists_run original values formula

/-- A valid ordinary-real predecessor model supplies a total diagnostic result. -/
theorem run_total (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, run values formula quantifier = some result := by
  obtain ⟨result, accepted, _⟩ := run_spec original values formula quantifier
  exact ⟨result, accepted⟩

/-- A true native production result is equivalent to the shared sentence
under the fixed coefficient valuation. -/
theorem run_true (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    run values formula quantifier = some true ↔
      (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => original.value (values i)) := by
  obtain ⟨result, accepted, semantic⟩ := run_spec original values formula quantifier
  simpa only [accepted, Option.some.injEq] using semantic

end Hex.RCF.RealCoefficients.Samples
