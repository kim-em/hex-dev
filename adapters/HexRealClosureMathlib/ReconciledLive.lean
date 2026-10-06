/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledLive
public import HexRealClosureMathlib.ReconciledGatherModel
public import HexRealClosureMathlib.LiveRequest

public section

namespace Hex.RealClosure.Tower.Live

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]

/-- Reconciled gathering succeeds for complete live requests whenever all
original owners fit the validated target. Every descriptor is revalidated
through its actual value-preserving map; no independent root agreement is used. -/
theorem Request.gatherReconciled?_models (following : base.Realization)
    (reference : Model (Context.ofBase base) K) (request : Request registry)
    (compatible : ∀ source ∈ request.owners,
      source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, request.gatherReconciled? base = some result ∧
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following reference)
        result.shared following reference) := by
  obtain ⟨shared, gathered, ⟨model⟩⟩ :=
    Shared.gatherReconciled?_models following reference request.owners compatible
  obtain ⟨frames, checked⟩ := request.transport?_success shared.maps model.target model.owners
  obtain ⟨result, produced, same⟩ :=
    request.gatherReconciled?_of_success base shared gathered frames checked
  exact ⟨result, produced, ⟨same.symm ▸ model⟩⟩

/-- Interpret an already accepted collection from its actual native gather,
deriving all owner and dependency-cache agreements from the target history. -/
noncomputable def Collection.reconciledModel {request : Request registry}
    (collection : Collection base request) (following : base.Realization)
    (reference : Model (Context.ofBase base) K)
    (produced : request.gatherReconciled? base = some collection) :
    Shared.Model (reader := OwnerReader.reconciled following reference)
      collection.shared following reference :=
  Shared.Model.ofReconciledGather following reference request.owners collection.shared
    (Request.gatherReconciled?_shared base request collection produced)

end Hex.RealClosure.Tower.Live

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciled?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciled?_models

/-- info: 'Hex.RealClosure.Tower.Live.Collection.reconciledModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.reconciledModel
