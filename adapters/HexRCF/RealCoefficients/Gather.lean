/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Samples
public import HexRealClosureTheory.CacheGather

public section
open scoped List
namespace Hex.RCF.RealCoefficients.Gather
open Hex RealClosure RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {owners : List (Context registry)}

/-! Coordinates from independently constructed native contexts are transported
through the owner's actual gathering result. An ordinary-real common model
retains every original coordinate and selected embedding. This module composes
native production and shared syntax; source authentication and frozen replay
remain separate adapter obligations. -/

/-- Keep each coefficient at its original owner before applying its checked map. -/
@[expose] def values (shared : Shared base owners)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value) :
    Fin owners.length → shared.input.context.Value :=
  fun i => shared.value i (coefficients i)

@[expose] noncomputable def valuation (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value) (x : ℝ) :
    Fin (owners.length + 1) → ℝ :=
  RealFormula.append (fun i => (models.get i).1.value (coefficients i)) x

theorem values_real (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value) :
    (fun i => target.value (values shared coefficients i)) =
      (fun i => (models.get i).1.value (coefficients i)) := by
  funext i
  exact models.value i (coefficients i)

/-- Every original shared atom has its original owner's coordinate meaning
at the same real variable after gathering and specialization. -/
theorem prepare_eval (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (x : ℝ) :
    (RepresentationSpecialize.prepare (values shared coefficients) formula).map
      (RepresentationSpecialize.evaluate target.value target.zero_iff x) =
      formula.polys.map (fun q => q.eval (valuation shared target models coefficients x)) := by
  have result := Samples.prepare_real target (values shared coefficients) formula x
  simp only [Samples.valuation, values_real shared target models coefficients] at result
  exact result

/-- Native production in one gathered context retains all original owner coordinates.
The conclusion is shared syntax at one real variable, not frozen replay. -/
theorem run_spec (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (models.get i).1.value (coefficients i))) := by
  have result := Samples.run_spec target (values shared coefficients) formula quantifier
  rw [values_real shared target models coefficients] at result
  exact result

/-- A returned gathering result retains separately authenticated original
owner models. Factory equations establish their agreement with the common model. -/
theorem run_original (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (shared : Shared base owners) (produced : Shared.gather? base owners = some shared)
    (original : (i : Fin owners.length) → Model (owners[i]) ℝ)
    (sourceModels : ∀ i, (owners[i]).model? following reference = some (original i))
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (original i).value (coefficients i))) := by
  let model := Shared.Model.ofGather following reference owners shared produced
  have aligned : (fun i => model.target.value (values shared coefficients i)) =
      (fun i => (original i).value (coefficients i)) := by
    funext i
    exact model.value_of_model i (original i) (sourceModels i) (coefficients i)
  have result := Samples.run_spec model.target (values shared coefficients) formula quantifier
  rw [aligned] at result
  exact result

/-- Ordered subsequences of registered constants suffice for actual gathering
and decision production. Every coefficient keeps its original owner's meaning;
additional target constants need not occur after the source constants. -/
theorem gather_subsequence (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ shared : Shared base owners, Shared.gather? base owners = some shared ∧
      ∃ model : Shared.Model shared following reference,
        ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) := by
  obtain ⟨shared, produced, ⟨model⟩⟩ :=
    Shared.gather?_models following reference owners compatible
  obtain ⟨result, accepted, semantic⟩ :=
    run_spec shared model.target model.owners coefficients formula quantifier
  exact ⟨shared, produced, model, result, accepted, semantic⟩

/-- Prefix-compatible callers retain their original gathering and decision API. -/
theorem gather_spec (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ shared : Shared base owners, Shared.gather? base owners = some shared ∧
      ∃ model : Shared.Model shared following reference,
        ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) :=
  gather_subsequence following reference
    (fun source member => ⟨(compatible source member).1.sublist,
      (compatible source member).2⟩) coefficients formula quantifier

end Hex.RCF.RealCoefficients.Gather
