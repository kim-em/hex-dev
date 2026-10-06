/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Gather
public import HexRealClosure.SharedPresentation

open Hex Hex.RealClosure Hex.RealClosure.Tower
open scoped List

public section
namespace Hex.RCF.RealCoefficients.Gather
variable {registry : BaseContext.Registry}

/-- Preserve an ordered nonempty list of original coefficient values from
`Context.ofBase provider.context.finish`. Insertion into an empty catalog
selects that same nonrational prefix and derives its identity factory.
An empty list selects the rational prefix through the existing API.
This is native production, not source authentication or frozen replay. -/
theorem run_registered_many (provider : BaseContext.RealPrefix.Model registry)
    (catalog : BaseContext.Catalog registry)
    (inserted : (BaseContext.Catalog.empty registry).insert provider.context = some catalog)
    (count : Nat) (positive : 0 < count)
    (coordinates : Fin (List.replicate count (Context.ofBase provider.context.finish)).length →
      (Context.ofBase provider.context.finish).Value)
    (formula : RealFormula.QF
      ((List.replicate count (Context.ofBase provider.context.finish)).length + 1))
    (quantifier : RealFormula.Quantifier) :
    ∃ result, runFrom?
      (owners := List.replicate count (Context.ofBase provider.context.finish)) catalog
      (fun i => cast (congrArg Context.Value (List.getElem_replicate i.isLt).symm)
        (coordinates i)) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => provider.towerModel.value (coordinates i))) := by
  have nonempty : provider.context.keys ≠ [] := by
    have unused := (BaseContext.Catalog.insert_isSome_iff _ _).mp
      (by rw [inserted]; rfl)
    intro emptyKeys
    rw [emptyKeys, BaseContext.Catalog.lookup_rational] at unused
    cases unused
  let owner := Context.ofBase provider.context.finish
  have origin : owner.origin.base = provider.context.finish :=
    Context.ofBase_origin_base provider.context.finish
  have mapped : (List.replicate count owner).map (·.origin.base) =
      List.replicate count provider.context.finish := by
    simp only [List.map_replicate, origin]
  have depth : SharedBase.depth ((List.replicate count owner).map (·.origin.base)) = 0 := by
    rw [mapped]
    simp only [SharedBase.depth]
    have zero : ∀ n, (List.replicate n provider.context.finish).foldl
        (fun acc source => max acc source.depth) 0 = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        simpa only [List.replicate_succ, List.foldl_cons, BaseContext.PackedContext.depth,
          BaseContext.RealPrefix.finish_signature, Nat.max_self] using ih
    exact zero count
  have member : provider.context ∈ catalog.prefixes :=
    (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mpr (Or.inl rfl)
  have success := SharedBase.choose?_success catalog
    ((List.replicate count owner).map (·.origin.base))
    provider.context member (by
      intro source present
      rw [mapped] at present
      have same := List.eq_of_mem_replicate present
      subst source
      simp only [BaseContext.RealPrefix.finish_signature]
      exact List.Sublist.refl _)
  cases selected : SharedBase.choose? catalog
      ((List.replicate count owner).map (·.origin.base)) with
  | none => simp only [selected, Option.isSome_none, Bool.false_eq_true] at success
  | some chosen =>
    have target : chosen.target = provider.context.finish := by
      obtain ⟨entry, present, target⟩ :=
        SharedBase.choose?_target catalog _ chosen selected
      rcases (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mp present with
        same | rational
      · rw [same, depth] at target
        exact target
      · rw [BaseContext.Catalog.prefixes_empty] at rational
        simp only [List.mem_singleton] at rational
        have keys := (SharedBase.compatible chosen owner.origin.base
          (List.mem_map.mpr ⟨owner, List.mem_replicate.mpr ⟨Nat.ne_of_gt positive, rfl⟩, rfl⟩)).1
        rw [origin] at keys
        rw [target, rational, depth] at keys
        simp only [BaseContext.PackedContext.extend_signature,
          BaseContext.RealPrefix.finish_signature, BaseContext.RealPrefix.keys,
          BaseContext.RealContext.keys, BaseContext.RealContext.keys_rational] at keys
        exact False.elim (nonempty (List.sublist_nil.mp keys))
    cases chosen with
    | mk chosenBase included =>
      dsimp only at target
      subst chosenBase
      have compatible : ∀ source ∈ (List.replicate count owner),
          source.origin.base.signature.constants <+ provider.context.finish.signature.constants ∧
            source.origin.base.signature.infinitesimals ≤
              provider.context.finish.signature.infinitesimals := by
        intro source present
        have same := List.eq_of_mem_replicate present
        subst source
        rw [origin]
        exact ⟨List.Sublist.refl _, Nat.le_refl _⟩
      obtain ⟨shared, produced, ⟨model⟩⟩ :=
        Shared.gather?_models provider.realization provider.towerModel
          (List.replicate count owner) compatible
      have gathered := Shared.gatherFrom?_of_success catalog (List.replicate count owner)
        ⟨provider.context.finish, included⟩ selected shared produced
      let originals : (i : Fin (List.replicate count owner).length) →
          Model ((List.replicate count owner)[i]) ℝ := fun i =>
        cast (congrArg (fun c => Model c ℝ) (List.getElem_replicate i.isLt).symm)
          provider.towerModel
      have factories : ∀ i, ((List.replicate count owner)[i]).model? provider.realization
          provider.towerModel = some (originals i) := by
        intro i
        have castFactory (c : Context registry) (same : c = owner) :
            c.model? provider.realization provider.towerModel =
              some (cast (congrArg (fun c => Model c ℝ) same.symm) provider.towerModel) := by
          cases same
          exact Context.model?_base provider.realization provider.towerModel
        exact castFactory _ (List.getElem_replicate i.isLt)
      obtain ⟨result, computed, semantic⟩ :=
        runFrom?_original catalog provider.realization provider.towerModel shared gathered
          originals factories (fun i => cast
            (congrArg Context.Value (List.getElem_replicate i.isLt).symm) (coordinates i))
          formula quantifier
      refine ⟨result, computed, ?_⟩
      convert semantic using 2
      funext i
      have castValue (c : Context registry) (same : c = owner) (a : owner.Value) :
          (cast (congrArg (fun c => Model c ℝ) same.symm) provider.towerModel).value
            (cast (congrArg Context.Value same.symm) a) = provider.towerModel.value a := by
        cases same
        rfl
      exact (castValue _ (List.getElem_replicate i.isLt) (coordinates i)).symm

/-- The one-coordinate API is the singleton case of ordered registered gathering. -/
theorem run_registered (provider : BaseContext.RealPrefix.Model registry)
    (catalog : BaseContext.Catalog registry)
    (inserted : (BaseContext.Catalog.empty registry).insert provider.context = some catalog)
    (a : (Context.ofBase provider.context.finish).Value)
    (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier) :
    ∃ result, runFrom? (owners := [Context.ofBase provider.context.finish]) catalog
      (Fin.cases a (fun i => Fin.elim0 i)) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun _ : Fin 1 => provider.towerModel.value a)) := by
  obtain ⟨result, produced, semantic⟩ :=
    run_registered_many provider catalog inserted 1 (by decide) (fun _ => a) formula quantifier
  refine ⟨result, ?_, semantic⟩
  have same : (Fin.cases a (fun i => Fin.elim0 i) :
      (i : Fin 1) → ([Context.ofBase provider.context.finish][i]).Value) =
      (fun i : Fin 1 => cast (congrArg Context.Value
        (List.getElem_replicate (n := 1) (a := Context.ofBase provider.context.finish)
          i.isLt).symm) a) := by
    funext i
    fin_cases i
    rfl
  exact (congrArg (fun coefficients => runFrom?
    (owners := [Context.ofBase provider.context.finish]) catalog coefficients formula quantifier)
    same).trans produced

end Hex.RCF.RealCoefficients.Gather
