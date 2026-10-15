/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellBuild
public import HexRealClosureTheory.Sample
public section
namespace Hex.RCF.RealCoefficients.SectorRequest
open Hex Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Context registry}

/-- Retain the sample value through its proved common-context identity. -/
@[expose] def valueOf (sample : Tower.Sample parent) (input : Conversion parent)
    (same : sample.input = input) : input.context.Value :=
  cast (congrArg (fun c : Conversion parent => c.context.Value) same) sample.value

theorem value_eq (sample : Tower.Sample parent) (input : Conversion parent)
    (same : sample.input = input) (original : Model parent ℝ)
    (target : Conversion.Model input original)
    (realization : Conversion.Model sample.input original) (aligned : HEq realization target) :
    target.target.value (valueOf sample input same) = realization.target.value sample.value := by
  subst input
  have equal : realization = target := eq_of_heq aligned
  subst realization
  rfl

/-- Request an ordinary value using the owner’s checked adjacent-boundary API. -/
@[expose] def point? {polynomials : List parent.Poly} (family : Tower.Sample.Partition parent polynomials)
    (lower upper : Hex.Endpoint family.collection.input.context.Value) :
    Option family.collection.input.context.Value :=
  match returned : family.sectorBetween? lower upper with
  | none => none
  | some sample => some (valueOf sample family.collection.input
      (family.sectors_input (family.sectorBetween?_mem lower upper sample returned)))

theorem point_inside {polynomials : List parent.Poly}
    (family : Tower.Sample.Partition parent polynomials) (original : Model parent ℝ)
    (model : Collection.Model family.collection original)
    (lower upper : Hex.Endpoint family.collection.input.context.Value)
    (point : family.collection.input.context.Value) (returned : point? family lower upper = some point) :
    (Tower.Cell.sector lower upper).Mem model.input.target (model.input.target.value point) := by
  unfold point? at returned
  split at returned
  · contradiction
  · rename_i sample found
    simp only [Option.some.injEq] at returned
    subst point
    obtain ⟨realization, aligned, checked, interval⟩ :=
      family.sectorBetween?_correct original model lower upper sample found
    rw [value_eq sample family.collection.input _ original model.input realization aligned]
    exact (interval _).mp ((Tower.Cell.contains_correct realization.target _ _).mp checked)

theorem point_exists {polynomials : List parent.Poly}
    (family : Tower.Sample.Partition parent polynomials) (original : Model parent ℝ)
    (model : Collection.Model family.collection original)
    (lower upper : Hex.Endpoint family.collection.input.context.Value)
    (adjacent : Tower.Cell.sector lower upper ∈ family.cells) :
    ∃ point, point? family lower upper = some point := by
  obtain ⟨sample, returned⟩ := family.sectorBetween?_success original model
    lower upper lower upper adjacent rfl rfl
  unfold point?
  split
  · rename_i missing
    rw [returned] at missing
    contradiction
  · exact ⟨_, rfl⟩

/-- Actual owner progress and membership give a point at the requested endpoints. -/
theorem point_witness {polynomials : List parent.Poly}
    (family : Tower.Sample.Partition parent polynomials) (original : Model parent ℝ)
    (model : Collection.Model family.collection original)
    (lower upper : Hex.Endpoint family.collection.input.context.Value)
    (adjacent : Tower.Cell.sector lower upper ∈ family.cells) :
    ∃ point, point? family lower upper = some point ∧
      (Tower.Cell.sector lower upper).Mem model.input.target (model.input.target.value point) := by
  obtain ⟨point, returned⟩ := point_exists family original model lower upper adjacent
  exact ⟨point, returned, point_inside family original model lower upper point returned⟩

namespace Cut
variable {polynomials : List parent.Poly}

@[expose] def lower (family : Tower.Sample.Partition parent polynomials)
    (cut : Fin (family.values.length+1)) : Endpoint family.collection.input.context.Value :=
  if zero : cut.val = 0 then .negInf
  else .finite (family.values[cut.val-1]'(by have := cut.isLt; omega))

@[expose] def upper (family : Tower.Sample.Partition parent polynomials)
    (cut : Fin (family.values.length+1)) : Endpoint family.collection.input.context.Value :=
  if inside : cut.val < family.values.length then .finite (family.values[cut.val]'inside)
  else .posInf

/-- Each finite cut names an actual sector, including both rays and the whole line. -/
theorem adjacent (family : Tower.Sample.Partition parent polynomials)
    (cut : Fin (family.values.length+1)) :
    Tower.Cell.sector (lower family cut) (upper family cut) ∈ family.cells := by
  by_cases zero : cut.val = 0
  · cases values : family.values with
    | nil => simpa [lower, upper, zero, values] using family.wholeLine_mem values
    | cons first rest =>
      simpa [lower, upper, zero, values] using family.leftRay_mem first rest values
  · have previous : cut.val-1 < family.values.length := by have := cut.isLt; omega
    by_cases inside : cut.val < family.values.length
    · have next : cut.val-1+1 = cut.val := by omega
      have expansion := (List.take_append_drop (cut.val-1) family.values).symm
      rw [List.drop_eq_getElem_cons previous, next, List.drop_eq_getElem_cons inside] at expansion
      simpa [lower, upper, zero, inside] using family.bounded_mem
        (family.values.take (cut.val-1)) (family.values.drop (cut.val+1))
        family.values[cut.val-1] family.values[cut.val] expansion
    · have final : cut.val-1+1 = family.values.length := by have := cut.isLt; omega
      have expansion : family.values = family.values.take (cut.val-1) ++ [family.values[cut.val-1]] := by
        simpa only [final, List.take_length] using (List.take_append_getElem previous).symm
      simpa [lower, upper, zero, inside] using family.rightRay_mem
        (family.values.take (cut.val-1)) family.values[cut.val-1] expansion

theorem witness (family : Tower.Sample.Partition parent polynomials)
    (original : Model parent ℝ) (model : Collection.Model family.collection original)
    (cut : Fin (family.values.length+1)) :
    ∃ point, SectorRequest.point? family (lower family cut) (upper family cut) = some point ∧
      (Tower.Cell.sector (lower family cut) (upper family cut)).Mem
        model.input.target (model.input.target.value point) :=
  SectorRequest.point_witness family original model _ _ (adjacent family cut)
end Cut

/-- Request every open cell in cut order through the owner's checked endpoint API. -/
@[expose] def points {polynomials : List parent.Poly}
    (family : Tower.Sample.Partition parent polynomials) :
    Option (Vector family.collection.input.context.Value (family.values.length+1)) :=
  Vector.ofFnM fun cut => point? family (Cut.lower family cut) (Cut.upper family cut)

/-- The executable requests succeed together, and each returned value belongs
 to its requested ordinary sector in the same compatible collection model. -/
theorem points_spec {polynomials : List parent.Poly}
    (family : Tower.Sample.Partition parent polynomials) (original : Model parent ℝ)
    (model : Collection.Model family.collection original) :
    ∃ values : Fin (family.values.length+1) → family.collection.input.context.Value,
      points family = some (Vector.ofFn values) ∧
      ∀ cut, (Tower.Cell.sector (Cut.lower family cut) (Cut.upper family cut)).Mem
        model.input.target (model.input.target.value (values cut)) := by
  choose values produced inside using Cut.witness family original model
  refine ⟨values, ?_, inside⟩
  unfold points
  have same : (fun cut => point? family (Cut.lower family cut) (Cut.upper family cut)) =
      (fun cut => pure (values cut)) := funext produced
  rw [same, Vector.ofFnM_pure]
  rfl
end Hex.RCF.RealCoefficients.SectorRequest
