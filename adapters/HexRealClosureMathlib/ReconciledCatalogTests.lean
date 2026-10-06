/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ReconciledCatalog
public import HexOrderedFnMathlib.LiouvilleTests

public section

namespace Hex.RealClosure.BaseContext.CatalogTests

open OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

def key : ConstantKey := ⟨"liouville", 1⟩
def registry : Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none

private theorem present : (registry key).isSome = true := by simp [registry, key]

noncomputable abbrev rationalModel := RealPrefix.Model.rational registry

private theorem providerTranscendence :
    letI : Field rationalModel.context.Carrier := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence rationalModel.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyMathlib.fieldOfGrind
  change Real.RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2)
  exact OrderedFn.LiouvilleTests.transcendence

private theorem providerContained (δ : Rat) (_positive : 0 < δ) :
    Contains ((registry key).get present δ) (liouvilleNumber 2) :=
  OrderedFn.LiouvilleTests.provider_contains δ

private theorem providerWidth (δ : Rat) (positive : 0 < δ) :
    ((registry key).get present δ).width ≤ δ :=
  OrderedFn.LiouvilleTests.provider_width δ positive

noncomputable def providerModel := rationalModel.register key present
  (liouvilleNumber 2) providerContained providerWidth providerTranscendence

noncomputable abbrev entry := providerModel.context

private theorem entry_keys : entry.keys = [key] := by
  exact (RealPrefix.Model.register_keys rationalModel key present
    (liouvilleNumber 2) providerContained providerWidth providerTranscendence).trans (by
      simp only [rationalModel, RealPrefix.Model.rational, RealPrefix.Model.context,
        RealPrefix.keys, RealContext.keys, RealContext.ofChain_chain, RealChain.keys,
        List.nil_append])

noncomputable def modeledCatalog := ((Catalog.empty registry).insert entry).getD
  (Catalog.empty registry)

private theorem modeled_insert :
    (Catalog.empty registry).insert entry = some modeledCatalog := by
  have available := (Catalog.insert_isSome_iff (Catalog.empty registry) entry).mpr
    (Catalog.lookup_empty registry entry.keys (by rw [entry_keys]; simp))
  cases inserted : (Catalog.empty registry).insert entry with
  | none => simp [inserted] at available
  | some next => simp [modeledCatalog, inserted]

/-- The concrete immutable reader catalog retains the actual analytic provider
premises rather than an independently asserted source interpretation. -/
theorem catalog_models : Catalog.Models modeledCatalog := by
  have inserted : (Catalog.empty registry).insert providerModel.context = some modeledCatalog := by
    exact modeled_insert
  exact (Catalog.Models.empty registry).insert providerModel inserted

noncomputable def providerBase : PackedContext registry := entry.finish.extend 1

/-- An actual validated Liouville base, with any stored algebraic suffix over
its infinitesimal, admits automatic target selection and gathering. -/
theorem automatic_provider (suffix : Tower.Suffix (Tower.Context.ofBase providerBase)) :
    (Tower.Shared.gatherReconciledFrom? modeledCatalog [suffix.context]).isSome = true := by
  apply Tower.Shared.gatherReconciledFrom?_success catalog_models [suffix.context] entry
  · have inserted : (Catalog.empty registry).insert entry = some modeledCatalog := modeled_insert
    exact (Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mpr (Or.inl rfl)
  · intro owner member
    have same := List.mem_singleton.mp member
    subst owner
    have sameBase : suffix.context.origin.base = providerBase := by
      generalize original : providerBase = base at suffix ⊢
      cases base with
      | pack native => exact Tower.Suffix.origin_base native suffix
    rw [sameBase]
    simp only [providerBase, PackedContext.extend_signature, RealPrefix.finish_signature, entry_keys]
    exact ⟨by simp, fun _ member => member⟩

/-- A supplied joint provider history is selected automatically for an
arbitrary algebraic suffix whose original providers occur in reversed order.
The only semantic premises are those stored in the actual inserted model. -/
theorem reverse_catalog {r : Registry} {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (original : Context r B sign)
    (suffix : Tower.Suffix (Tower.Context.base original))
    (provider : RealPrefix.Model r) (catalog : Catalog r)
    (inserted : (Catalog.empty r).insert provider.context = some catalog)
    (α β : ConstantKey) (different : α ≠ β)
    (sourceKeys : original.signature.constants = [α, β])
    (targetKeys : provider.context.keys = [β, α]) :
    (Tower.Shared.gatherReconciledFrom? catalog [suffix.context]).isSome = true := by
  apply Tower.Shared.gatherReconciledFrom?_success
    ((Catalog.Models.empty r).insert provider inserted) [suffix.context] provider.context
  · exact (Catalog.mem_prefixes_of_insert _ _ _ _ inserted).mpr (Or.inl rfl)
  · intro owner member
    have same := List.mem_singleton.mp member
    subst owner
    rw [Tower.Suffix.origin_base original suffix]
    change original.signature.constants.Nodup ∧
      original.signature.constants ⊆ provider.context.keys
    rw [sourceKeys, targetKeys]
    refine ⟨by simp [different], ?_⟩
    intro k member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl

end Hex.RealClosure.BaseContext.CatalogTests

/-- info: 'Hex.RealClosure.BaseContext.CatalogTests.catalog_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.CatalogTests.catalog_models

/-- info: 'Hex.RealClosure.BaseContext.CatalogTests.automatic_provider' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.CatalogTests.automatic_provider

/-- info: 'Hex.RealClosure.BaseContext.CatalogTests.reverse_catalog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.CatalogTests.reverse_catalog
