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

/-- For a catalog containing only the caller's authenticated real prefix,
select that exact prefix and preserve the original coefficient value. The
factory identity is derived, not a caller premise. This is native production;
it does not authenticate source expressions or replace frozen replay. -/
theorem run_registered (provider : BaseContext.RealPrefix.Model registry)
    (nonempty : provider.context.keys ≠ [])
    (catalog : BaseContext.Catalog registry)
    (inserted : (BaseContext.Catalog.empty registry).insert provider.context = some catalog)
    (a : (Context.ofBase provider.context.finish).Value)
    (formula : RealFormula.QF 2) (quantifier : RealFormula.Quantifier) :
    ∃ result, runFrom? (owners := [Context.ofBase provider.context.finish]) catalog
      (Fin.cases a (fun i => Fin.elim0 i)) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun _ : Fin 1 => provider.towerModel.value a)) := by
  let owner := Context.ofBase provider.context.finish
  have origin : owner.origin.base = provider.context.finish :=
    Context.ofBase_origin_base provider.context.finish
  have mapped : [owner].map (·.origin.base) = [provider.context.finish] := by
    simp only [List.map_cons, List.map_nil, origin]
  have depth : SharedBase.depth ([owner].map (·.origin.base)) = 0 := by
    rw [mapped]
    simp only [SharedBase.depth, List.foldl_cons, List.foldl_nil,
      BaseContext.PackedContext.depth, BaseContext.RealPrefix.finish_signature, Nat.max_self]
  have member : provider.context ∈ catalog.prefixes :=
    (BaseContext.Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mpr (Or.inl rfl)
  have success := SharedBase.choose?_success catalog ([owner].map (·.origin.base))
    provider.context member (by
      intro source present
      rw [mapped] at present
      simp only [List.mem_singleton] at present
      subst source
      simp only [BaseContext.RealPrefix.finish_signature]
      exact List.Sublist.refl _)
  cases selected : SharedBase.choose? catalog ([owner].map (·.origin.base)) with
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
          (List.mem_map.mpr ⟨owner, List.mem_singleton_self _, rfl⟩)).1
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
      have compatible : ∀ source ∈ [owner],
          source.origin.base.signature.constants <+ provider.context.finish.signature.constants ∧
            source.origin.base.signature.infinitesimals ≤ provider.context.finish.signature.infinitesimals := by
        intro source present
        simp only [List.mem_singleton] at present
        subst source
        rw [origin]
        exact ⟨List.Sublist.refl _, Nat.le_refl _⟩
      obtain ⟨shared, produced, ⟨model⟩⟩ :=
        Shared.gather?_models provider.realization provider.towerModel [owner] compatible
      have gathered := Shared.gatherFrom?_of_success catalog [owner]
        ⟨provider.context.finish, included⟩ selected shared produced
      let originals : (i : Fin 1) → Model ([owner][i]) ℝ :=
        Fin.cases provider.towerModel (fun i => Fin.elim0 i)
      have factories : ∀ i : Fin 1, ([owner][i]).model? provider.realization
          provider.towerModel = some (originals i) := by
        intro i
        fin_cases i
        exact Context.model?_base provider.realization provider.towerModel
      obtain ⟨result, computed, semantic⟩ :=
        runFrom?_original catalog provider.realization provider.towerModel shared gathered
          originals factories (Fin.cases a (fun i => Fin.elim0 i)) formula quantifier
      refine ⟨result, computed, ?_⟩
      convert semantic using 2
      funext i
      fin_cases i
      rfl

end Hex.RCF.RealCoefficients.Gather
