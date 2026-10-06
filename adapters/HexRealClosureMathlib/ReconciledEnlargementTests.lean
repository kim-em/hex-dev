/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ReconciledRealization
public import HexRealClosureMathlib.ReconciledCatalogTests
public import HexRealClosureMathlib.ReconciledGatherTests

public section

namespace Hex.RealClosure.Tower.ReconciledEnlargementTests

open Live

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {parent : Context registry}
variable {K : Type} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]

/-- An importing consumer can apply descriptor soundness to the public root
interpretation appearing in the twice-enlarged collection theorem. -/
example (model : Model parent K)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature) :
    selectedValue model descriptor ∈ HexRealRootsMathlib.Tarski.rootsIn
      (HexPolyMathlib.Interpret.interpret model.value model.zero_iff descriptor.raw.head)
      (descriptor.raw.lower.map model.value) (descriptor.raw.upper.map model.value) := by
  exact (descriptor.root_spec model.value model.zero_iff model.one model.add
    model.sub model.mul model.nat model.sign).1

/-- The importing consumer obtains every frame's composed interpretation from
public models and two actual successful calls, without supplied agreement. -/
theorem preserve_frames {base : BaseContext.PackedContext registry}
    {request : Request registry} (original : Live.Collection base request)
    (following : base.Realization) (reference : Model (Context.ofBase base) K)
    (gathered : request.gatherReconciled? base = some original)
    (ambient : Ambient (Hex.RationalFn K)) (first : Live.Enlargement original)
    (firstProduced : original.enlarge? = some first)
    (nextAmbient : Ambient (Hex.RationalFn ambient.Carrier)) (twice : Live.Enlargement first.collection)
    (twiceProduced : first.collection.enlarge? = some twice) :
    let initial := original.reconciledModel following reference gathered
    let once := first.reconciledModel initial ambient firstProduced
    let returned := (twice.reconciledModel once nextAmbient twiceProduced).target
    let inclusion := (Ambient.coefficientHom nextAmbient).comp (Ambient.coefficientHom ambient)
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map returned.value = frame.values.map (fun v => inclusion (initial.target.value v)) ∧
      refreshed.polynomials.map (HexPolyMathlib.Interpret.interpret returned.value returned.zero_iff) =
        frame.polynomials.map (fun p =>
          (HexPolyMathlib.Interpret.interpret initial.target.value initial.target.zero_iff p).map inclusion) ∧
      refreshed.descriptors.map (selectedValue returned) =
        frame.descriptors.map (fun d => inclusion (selectedValue initial.target d)))
      original.frames twice.collection.frames :=
  original.preserveReconciled_twice following reference gathered ambient first firstProduced nextAmbient twice twiceProduced

noncomputable abbrev providerBase := BaseContext.CatalogTests.providerModel.context.finish.extend 1

/-- An actual Liouville history and a complete selected-root request survive
two successful enlargements without any supplied realization, reference model,
factory success or coefficient-agreement hypothesis. Each new parameter is
below every positive value in its actual predecessor target. -/
theorem provider_twice
    (root : Root (Context.ofBase providerBase)) :
    ∃ collection : Live.Collection providerBase (rootRequest root),
      (rootRequest root).gatherReconciled? providerBase = some collection ∧
        ∃ first : Live.Enlargement collection, collection.enlarge? = some first ∧
          ∃ twice : Live.Enlargement first.collection, first.collection.enlarge? = some twice ∧
            first.collection.shared.input.context.sign first.parameter = 1 ∧
            twice.collection.shared.input.context.sign twice.parameter = 1 ∧
            (∀ a, collection.shared.input.context.sign a = 1 →
              first.collection.shared.input.context.sign
                (first.parameter - first.previous.value a) = -1) ∧
            (∀ a, first.collection.shared.input.context.sign a = 1 →
              twice.collection.shared.input.context.sign
                (twice.parameter - twice.previous.value a) = -1) := by
  classical
  let following : providerBase.Realization :=
    BaseContext.CatalogTests.providerModel.staged 1
  let reference := following.reference
  have originBase : (Context.ofBase providerBase).origin.base =
      providerBase := by
    generalize providerBase = base
    cases base with
    | pack original => rfl
  have rootsBase : ∀ owner ∈ (rootRequest root).owners,
      owner.origin.base = providerBase := by
    cases root with
    | point value =>
      intro owner member
      simp only [rootRequest, Request.owners, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst owner
      exact originBase
    | selected descriptor extension built =>
      intro owner member
      simp only [rootRequest, Request.owners, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · subst owner; exact originBase
      · subst owner
        exact (Root.selected descriptor extension built).origin_base.trans originBase
  obtain ⟨collection, gathered, _⟩ := Request.gatherReconciled?_models following
    reference.model (rootRequest root) (by
      intro owner member
      rw [rootsBase owner member]
      exact ⟨following.keys_nodup, fun _ present => present, le_rfl⟩)
  let initial := collection.reconciledModel following reference.model gathered
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  obtain ⟨first, produced, _⟩ := collection.enlargeReconciled?_models initial ambient
  let once := first.reconciledModel initial ambient produced
  let nextAmbient := Ambient.ofField (Hex.RationalFn ambient.Carrier)
  obtain ⟨twice, twiceProduced, _⟩ := first.collection.enlargeReconciled?_models once nextAmbient
  have firstOrdered := first.ordered reference.model
  have nextOrdered := twice.ordered (Model.next _ reference.model ambient)
  exact ⟨collection, gathered, first, produced, twice, twiceProduced,
    firstOrdered.1, nextOrdered.1, firstOrdered.2, nextOrdered.2⟩

/-- Reconciliation over genuinely reversed provider paths remains accepted
when the target grows, for every stored algebraic suffix. The ordered gather
continues to reject; source models and cache coherence are derived. -/
theorem reverse_enlarge {r : BaseContext.Registry} {R : Type u}
    [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context r B sign) (suffix : Suffix (Context.base original))
    (base : BaseContext.PackedContext r) (following : base.Realization)
    (reference : Model (Context.ofBase base) R)
    (α β : BaseContext.ConstantKey) (different : α ≠ β)
    (sourceSignature : (BaseContext.PackedContext.pack original).signature = ⟨[α, β], 1⟩)
    (targetSignature : base.signature = ⟨[β, α], 2⟩)
    (ambient : Ambient (Hex.RationalFn R)) :
    (BaseContext.PackedContext.pack original).subsequence? base = none ∧
      ∃ shared : Shared base [suffix.context],
        Shared.gatherReconciled? base [suffix.context] = some shared ∧
          ∃ result : SharedEnlargement shared, shared.enlarge? = some result ∧
            Nonempty (Shared.Model (reader := OwnerReader.reconciled following.infinitesimal
              (Model.next base reference ambient)) result.shared following.infinitesimal
              (Model.next base reference ambient)) := by
  obtain ⟨rejected, shared, gathered, model, _⟩ := ReconciledTests.reverse_keys
    original suffix base following reference α β different sourceSignature targetSignature
  obtain ⟨result, produced, returned, _⟩ := model.enlargeReconciled ambient
  exact ⟨rejected, shared, gathered, result, produced, ⟨returned⟩⟩

/-- After two actual reconciled enlargements, one ordinary partial reader
fixes every inherited provider coefficient along both predecessor maps and
gives the new parameter a positive ordinary value. -/
theorem provider_twice_realized (root : Root (Context.ofBase providerBase)) :
    ∃ collection : Live.Collection providerBase (rootRequest root),
      ∃ first : Live.Enlargement collection, ∃ next : Live.Enlargement first.collection,
        (rootRequest root).gatherReconciled? providerBase = some collection ∧
          collection.enlarge? = some first ∧ first.collection.enlarge? = some next ∧
          ∃ read : next.collection.shared.input.context.Value → ℝ,
            ∃ domain : next.collection.shared.input.context.Value → Prop,
              Transport.Closed read domain ∧ domain next.parameter ∧ 0 < read next.parameter ∧
              ∀ b r, BaseContext.PackedContext.Realization.RealValue
                  (BaseContext.CatalogTests.providerModel.staged 1) b r →
                domain (next.previous.value (first.previous.value (collection.shared.input.value b))) ∧
                read (next.previous.value (first.previous.value (collection.shared.input.value b))) = r := by
  classical
  obtain ⟨collection, gathered, first, built, next, produced, _⟩ := provider_twice root
  let following : providerBase.Realization := BaseContext.CatalogTests.providerModel.staged 1
  let reference := following.reference
  let initial := collection.reconciledModel following reference.model gathered
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  let once := first.reconciledModel initial ambient built
  obtain ⟨read, domain, data⟩ := next.realizeReconciled_model once produced []
  refine ⟨collection, first, next, gathered, built, produced, read, domain,
    data.closed, data.parameter, data.positive, ?_⟩
  intro b r real
  obtain ⟨inherited, coefficient, aligned⟩ := first.reconciled_coefficient initial ambient built
    b r real (collection.shared.input.value b) (initial.input b)
  exact data.representativeFixed inherited r coefficient _ aligned

end Hex.RealClosure.Tower.ReconciledEnlargementTests

/-- info: 'Hex.RealClosure.Tower.ReconciledEnlargementTests.preserve_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledEnlargementTests.preserve_frames

/-- info: 'Hex.RealClosure.Tower.ReconciledEnlargementTests.provider_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledEnlargementTests.provider_twice

/-- info: 'Hex.RealClosure.Tower.ReconciledEnlargementTests.reverse_enlarge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledEnlargementTests.reverse_enlarge

/-- info: 'Hex.RealClosure.Tower.ReconciledEnlargementTests.provider_twice_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledEnlargementTests.provider_twice_realized
