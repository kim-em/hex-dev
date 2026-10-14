/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RepresentationCells
public import HexRCF.RealCoefficients.SectorSamples
public import HexRCF.RealCoefficients.PointRows
public section
namespace Hex.RCF.RealCoefficients.CellReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RealFormula
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value}

/-- Finite assembly of already checked root and selected-sign packets. Literal
parsing constructs these records separately; these fields assume no semantic
coverage, cell membership or sign-constancy proposition. -/
structure Evidence (roots : RootReplay.Result p .negInf .posInf)
    (values : Fin n → parent.Value) (formula : QF (n+1)) where
  sections : (i : Fin roots.roots.length) →
    SelectedSigns (roots.roots.get i) (RepresentationSpecialize.prepare values formula)
  sectors : (cut : Fin (roots.roots.length+1)) → SectorSamples.Sector roots cut
  sectorRows : (cut : Fin (roots.roots.length+1)) →
    PointRows.Packet (sectors cut).point values formula

variable {roots : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {formula : QF (n+1)}

@[expose] def Evidence.row (data : Evidence roots values formula) : Cell roots.roots.length → List Int
  | .root i => (data.sections i).values.toList
  | .open cut => (data.sectorRows cut).signs.values.toList

@[expose] noncomputable def Evidence.sample (data : Evidence roots values formula)
    (model : Model parent ℝ) : Cell roots.roots.length → ℝ
  | .root i => RootCells.points roots model i
  | .open cut => model.value (data.sectors cut).point

/-- Every assembled sample is an actual point in its particular cell. -/
theorem Evidence.inside (data : Evidence roots values formula) (model : Model parent ℝ)
    (cell : Cell roots.roots.length) :
    Cell.Region (RootCells.points roots model) cell (data.sample model cell) := by
  cases cell with
  | root i => rfl
  | «open» cut => exact (data.sectors cut).inside model

/-- All original atom occurrences in each row share its one ordinary sample. -/
theorem Evidence.exactRow (data : Evidence roots values formula) (model : Model parent ℝ)
    (cell : Cell roots.roots.length) :
    data.row cell = formula.polys.map (fun q =>
      (SignType.sign (q.eval (append (fun i => model.value (values i))
        (data.sample model cell))) : Int)) := by
  cases cell with
  | «open» cut => exact (data.sectorRows cut).row model
  | root i =>
    change (data.sections i).values.toList = _
    rw [(data.sections i).values_at_root model.value model.zero_iff model.one model.add
      model.sub model.mul model.nat model.sign]
    have evaluated := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
      (Samples.prepare_real model values formula (RootCells.points roots model i))
    simpa only [signsAt, List.map_map, Function.comp_def, RepresentationSpecialize.evaluate,
      Samples.valuation, Evidence.sample, RootCells.points] using evaluated
/-- Strictly visit every assembled cell, including after a decisive Boolean. -/
@[expose] def Evidence.run (data : Evidence roots values formula) (quantifier : Quantifier) : Option Bool :=
  match quantifier with
  | .forallReal => OptionFold.allArray (Cell.all roots.roots.length) (fun c => Samples.Row.eval formula (data.row c))
  | .existsReal => OptionFold.anyArray (Cell.all roots.roots.length) (fun c => Samples.Row.eval formula (data.row c))

/-- Check original divisors before the radical identities and strict fold.
The typed packets have already passed their individual literal readers. -/
@[expose] def check (values : Fin n → parent.Value) (formula : QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : Evidence roots values formula) (quantifier : Quantifier) : Except Replay.Error Bool :=
  if guards.all (fun d => Decidable.decide (d ≠ 0)) = true then
    if cert.check parent.signature (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true then
      match data.run quantifier with
      | none => .error .binding
      | some verdict => .ok verdict
    else .error .binding
  else .error .divisor

theorem check_parts (values : Fin n → parent.Value) (formula : QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : Evidence roots values formula) (quantifier : Quantifier) (verdict : Bool)
    (accepted : check values formula guards cert roots data quantifier = .ok verdict) :
    guards.all (fun d => Decidable.decide (d ≠ 0)) = true ∧
    cert.check parent.signature (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true ∧
    data.run quantifier = some verdict := by
  unfold check at accepted
  split at accepted
  · rename_i domains
    split at accepted
    · rename_i radical
      cases evaluated : data.run quantifier with
      | none => simp only [evaluated] at accepted; cases accepted
      | some result =>
        simp only [evaluated] at accepted
        cases accepted
        exact ⟨domains, radical, rfl⟩
    · cases accepted
  · cases accepted

theorem check_domains (model : Model parent ℝ)
    (values : Fin n → parent.Value) (formula : QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : Evidence roots values formula) (quantifier : Quantifier) (verdict : Bool)
    (accepted : check values formula guards cert roots data quantifier = .ok verdict) :
    ∀ d ∈ guards, model.value d ≠ 0 := by
  have domains := (check_parts values formula guards cert roots data quantifier verdict accepted).1
  intro d member zero
  exact (of_decide_eq_true (List.all_eq_true.mp domains d member)) ((model.zero_iff d).mp zero)

/-- Actual checked root coverage, radical identities, boundary signs and
whole rows entail the original shared quantified formula. -/
theorem check_sound (model : Model parent ℝ)
    (values : Fin n → parent.Value) (formula : QF (n+1))
    (guards : List parent.Value) (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : Evidence roots values formula) (quantifier : Quantifier)
    (accepted : check values formula guards cert roots data quantifier = .ok true) :
    (Prenex.quant quantifier (.matrix formula)).toProp (fun i => model.value (values i)) := by
  obtain ⟨_, radical, evaluated⟩ := check_parts values formula guards cert roots data quantifier true accepted
  cases quantifier with
  | forallReal =>
    exact (RepresentationCells.forall_rows values formula cert radical roots model
      (data.sample model) (data.inside model) data.row (data.exactRow model)).mp evaluated
  | existsReal =>
    exact (RepresentationCells.exists_rows values formula cert radical roots model
      (data.sample model) (data.inside model) data.row (data.exactRow model)).mp evaluated

end Hex.RCF.RealCoefficients.CellReplay
