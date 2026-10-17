/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ConstructedCatalog
public import HexRealClosure.ReconciledBase

public section
namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Every requested owner's provider keys, retaining their original order.
The native history constructor skips keys that are already present. -/
@[expose] def Live.Request.providerKeys (request : Live.Request registry) :
    List BaseContext.ConstantKey :=
  request.owners.flatMap fun owner => owner.origin.base.signature.constants

/-- Build or reuse a joint provider history, then reconcile every live frame
at that exact target and the maximum requested infinitesimal depth. The return
value retains the updated catalog for later reads and requests. -/
def Live.Request.gatherConstructed? (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key)) (parent : BaseContext.RealPrefix registry) :
    Option (Σ packet : catalog.Construction read parent request.providerKeys,
      Live.Collection (packet.target.finish.extend
        (SharedBase.depth (request.owners.map (·.origin.base)))) request) := do
  let packet ← catalog.construct? read parent request.providerKeys
  let collection ← request.gatherReconciled?
    (packet.target.finish.extend (SharedBase.depth (request.owners.map (·.origin.base))))
  return ⟨packet, collection⟩

/-- The final collection uses the exact constructed history and retains its
installation packet, including the catalog returned for subsequent requests. -/
theorem Live.Request.gatherConstructed?_of_success (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key)) (parent : BaseContext.RealPrefix registry)
    (packet : catalog.Construction read parent request.providerKeys)
    (constructed : catalog.construct? read parent request.providerKeys = some packet)
    (collection : Live.Collection (packet.target.finish.extend
      (SharedBase.depth (request.owners.map (·.origin.base)))) request)
    (gathered : request.gatherReconciled? (packet.target.finish.extend
      (SharedBase.depth (request.owners.map (·.origin.base)))) = some collection) :
    request.gatherConstructed? catalog read parent = some ⟨packet, collection⟩ := by
  simp only [Live.Request.gatherConstructed?, constructed, bind, Option.bind, gathered, pure]

/-- Acceptance recovers both the construction and reconciliation equations for
the exact returned packet; no installed history is selected in their place. -/
theorem Live.Request.gatherConstructed?_gathered (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key)) (parent : BaseContext.RealPrefix registry)
    (packet : catalog.Construction read parent request.providerKeys)
    (collection : Live.Collection (packet.target.finish.extend
      (SharedBase.depth (request.owners.map (·.origin.base)))) request)
    (accepted : request.gatherConstructed? catalog read parent = some ⟨packet, collection⟩) :
    catalog.construct? read parent request.providerKeys = some packet ∧
      request.gatherReconciled? (packet.target.finish.extend
        (SharedBase.depth (request.owners.map (·.origin.base)))) = some collection := by
  unfold Live.Request.gatherConstructed? at accepted
  cases produced : catalog.construct? read parent request.providerKeys with
  | none => simp only [produced, bind, Option.bind, reduceCtorEq] at accepted
  | some actual =>
    simp only [produced, bind, Option.bind] at accepted
    cases gathered : request.gatherReconciled? (actual.target.finish.extend
        (SharedBase.depth (request.owners.map (·.origin.base)))) with
    | none => simp only [gathered, reduceCtorEq] at accepted
    | some result =>
      simp only [gathered, pure] at accepted
      cases Option.some.inj accepted
      exact ⟨rfl, gathered⟩

end Hex.RealClosure.Tower
