/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.NativeRealization
public import HexRealClosureTheory.SharedRealization
public import HexRealClosure.TowerEnlarge
public import HexOrderedFnTheory.LiouvilleTests

namespace Hex.RealClosure.Tower.NativeRealizationTests

variable {registry : BaseContext.Registry} {B : Type}
variable [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
variable (base : BaseContext.Context registry B sign)
variable (following : base.chain.Realization registry)

private abbrev initial := Context.base base
variable (first : SignDet.Descriptor (initial base).Value Signature
  (initial base).sign (initial base).signature)
private abbrev middle := ((initial base).adjoin first).context
variable (second : SignDet.Descriptor (middle base first).Value Signature
  (middle base first).sign (middle base first).signature)
private abbrev suffix : Suffix (initial base) := .root first (.root second .nil)

/-- External consumers obtain one pair of real numbers preserving the signs
of both operands, their sum and their product after two actual root adjunctions.
The base may contain any number of successive native infinitesimals. -/
example (a b : (suffix base first second).context.Value) :
    ∃ x y : ℝ,
      (SignType.sign x : Int) = (suffix base first second).context.sign a ∧
      (SignType.sign y : Int) = (suffix base first second).context.sign b ∧
      (SignType.sign (x + y) : Int) = (suffix base first second).context.sign (a + b) ∧
      (SignType.sign (x * y) : Int) = (suffix base first second).context.sign (a * b) := by
  let packed : (BaseContext.PackedContext.pack base).Realization := following
  let history : (suffix base first second).context.origin.base.Realization :=
    ((suffix base first second).origin_base base).symm ▸ packed
  obtain ⟨read, domain, closed, finite, real⟩ :=
    (suffix base first second).context.realize_values history [a, b, a + b, a * b]
  have left := finite a (by simp)
  have right := finite b (by simp)
  have sum := finite (a + b) (by simp)
  have product := finite (a * b) (by simp)
  refine ⟨read a, read b,
    left.2, right.2, ?_, ?_⟩
  · rw [← closed.read_add a b left.1 right.1]
    exact sum.2
  · rw [← closed.read_mul a b left.1 right.1]
    exact product.2

/-- A fixed caller real coefficient is directly available after both roots;
its exact value, as well as a sum's sign, survives the same realization. -/
example (a : (suffix base first second).context.Value)
    (c : (initial base).Value) (r : ℝ) (inherited : following.RealValue c.stored r) :
    ∃ x : ℝ,
      (SignType.sign x : Int) = (suffix base first second).context.sign a ∧
      (SignType.sign (x + r) : Int) =
        (suffix base first second).context.sign (a + (suffix base first second).embed c) := by
  obtain ⟨read, domain, closed, finite, real⟩ := (suffix base first second).realize_values
    base following [a, a + (suffix base first second).embed c]
  have operand := finite a (by simp)
  have sum := finite (a + (suffix base first second).embed c) (by simp)
  have coefficient := real c r inherited
  refine ⟨read a, operand.2, ?_⟩
  rw [← coefficient.2, ← closed.read_add a _ operand.1 coefficient.1]
  exact sum.2

end Hex.RealClosure.Tower.NativeRealizationTests

namespace Hex.RealClosure.Tower.RegisteredRealizationTests

open scoped Hex.OrderedFn.Infinitesimal

open BaseContext OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private def key : ConstantKey := ⟨"liouville", 1⟩
private def registry : Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none
private theorem present : (registry key).isSome = true := by simp [registry, key]
private noncomputable abbrev rational := RealPrefix.Model.rational registry

private theorem transcendence :
    letI : Field rational.context.Carrier := HexPolyTheory.fieldOfGrind
    Real.RelativeTranscendence rational.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyTheory.fieldOfGrind
  change Real.RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2)
  exact OrderedFn.LiouvilleTests.transcendence

private theorem contained (δ : Rat) (_positive : 0 < δ) :
    Contains ((registry key).get present δ) (liouvilleNumber 2) := by
  exact OrderedFn.LiouvilleTests.provider_contains δ

private theorem width (δ : Rat) (positive : 0 < δ) :
    ((registry key).get present δ).width ≤ δ := by
  exact OrderedFn.LiouvilleTests.provider_width δ positive

private noncomputable def provider := rational.register key present
  (liouvilleNumber 2) contained width transcendence
private noncomputable abbrev staged := provider.context.finish.infinitesimal
private noncomputable def following : staged.Realization := provider.realization.infinitesimal
private noncomputable abbrev initial := Context.ofBase staged

private noncomputable def realCoefficient :
    (Context.ofBase provider.context.finish).Value := ⟨RationalFn.X⟩
private noncomputable def coefficient : initial.Value :=
  Context.baseValue staged
    (RationalFn.C (Context.baseStored provider.context.finish realCoefficient))
private noncomputable def epsilon : initial.Value := Context.baseValue staged RationalFn.X

private theorem coefficient_value :
    PackedContext.Realization.RealValue following coefficient (liouvilleNumber 2) := by
  apply (PackedContext.Realization.realValue_infinitesimal provider.realization
    realCoefficient (liouvilleNumber 2)).mpr
  apply (provider.realValue realCoefficient (liouvilleNumber 2)).mpr
  simp only [provider, RealPrefix.Model.register, RealPrefix.Model.rational,
    RealPrefix.Model.interpretation, RealPrefix.Interpretation.hom, realCoefficient,
    Context.baseStored]
  exact RealChain.interpretStep_X _ _ _ _ _ _ _ _ _ _

private noncomputable def head : DensePoly initial.Value := DensePoly.monomial 1 1
private noncomputable abbrev reference := following.reference

/-- The actual shared producer returns a descriptor over the concrete
registered-constant and infinitesimal base. Its linear polynomial has root zero. -/
private theorem producer :
    ∃ roots, SignDet.Descriptor.buildRoots initial.sign initial.signature head
      .negInf .posInf = .ok (some roots) ∧ roots ≠ [] := by
  let model := reference.model
  have polynomial : HexPolyTheory.Interpret.interpret model.value model.zero_iff head =
      (Polynomial.X : Polynomial reference.Carrier) := by
    ext n
    by_cases equal : n = 1
    · simp [head, HexPolyTheory.Interpret.coeff_interpret, DensePoly.coeff_monomial,
        Polynomial.coeff_X, equal, model.one]
    · simp only [head, HexPolyTheory.Interpret.coeff_interpret, DensePoly.coeff_monomial,
        Polynomial.coeff_X, ite_eq_right equal, ite_eq_right (Ne.symm equal)]
      exact (model.zero_iff 0).mpr rfl
  have domain : HexSturmTheory.Domain model.value model.zero_iff head .negInf .posInf := by
    rw [HexSturmTheory.Domain, polynomial]
    exact ⟨Polynomial.X_ne_zero, Polynomial.irreducible_X.squarefree, trivial, trivial, trivial⟩
  obtain ⟨roots, built, cover, _, _⟩ := SignDet.Descriptor.buildRoots_roots
    model.value model.zero_iff model.one model.add model.sub model.mul model.nat
    model.sign model.neg model.inv initial.signature head .negInf .posInf domain
  have root : (0 : reference.Carrier) ∈ HexRealRootsTheory.Tarski.rootsIn
      (HexPolyTheory.Interpret.interpret model.value model.zero_iff head) .negInf .posInf := by
    rw [polynomial, HexRealRootsTheory.Tarski.mem_rootsIn_iff _ Polynomial.X_ne_zero]
    simp
  refine ⟨roots, built, ?_⟩
  intro empty
  have member := (cover 0).mp root
  simp [empty] at member

/-- A producer-built adjunction over the actual Liouville prefix and its
infinitesimal preserves the registered real coefficient with no origin cast. -/
theorem realized :
    ∃ descriptor : SignDet.Descriptor initial.Value Signature initial.sign initial.signature,
      ∃ roots,
        SignDet.Descriptor.buildRoots initial.sign initial.signature head .negInf .posInf =
          .ok (some roots) ∧ descriptor ∈ roots ∧
        ∃ read : (initial.adjoin descriptor).context.Value → ℝ,
          ∃ domain : (initial.adjoin descriptor).context.Value → Prop,
            Transport.Closed read domain ∧
            domain ((initial.adjoin descriptor).embed coefficient) ∧
            read ((initial.adjoin descriptor).embed coefficient) = liouvilleNumber 2 ∧
            domain ((initial.adjoin descriptor).embed epsilon) ∧
            0 < read ((initial.adjoin descriptor).embed epsilon) := by
  obtain ⟨roots, built, nonempty⟩ := producer
  obtain ⟨descriptor, member⟩ := List.exists_mem_of_ne_nil roots nonempty
  let suffix : Suffix initial := .root descriptor .nil
  obtain ⟨read, domain, closed, finite, real⟩ := suffix.realize_packed staged following
    [suffix.embed epsilon]
  have fixed := real coefficient (liouvilleNumber 2) coefficient_value
  have positive := finite (suffix.embed epsilon) (by simp)
  have native : (initial.adjoin descriptor).context.sign
      ((initial.adjoin descriptor).embed epsilon) = 1 := by
    rw [(reference.model.adjoin descriptor).sign, reference.model.adjoin_embed,
      ← reference.model.sign]
    exact provider.realization.parameter_sign
  have sign : (SignType.sign (read (suffix.embed epsilon)) : Int) = 1 :=
    positive.2.trans native
  have realSign : SignType.sign (read (suffix.embed epsilon)) = 1 := by
    cases value : SignType.sign (read (suffix.embed epsilon)) <;> simp_all
  exact ⟨descriptor, roots, built, member, read, domain, closed,
    fixed.1, fixed.2, positive.1, sign_eq_one_iff.mp realSign⟩

/-- An actual gather and enlargement over the registered Liouville prefix
retain the coefficient's prescribed value under the same positive ordinary
parameter reader. The consumer supplies no origin equality or native equality
proof and constructs both successful producer results. -/
theorem shared_realized :
    ∃ collection : Live.Collection staged ([] : Live.Request registry),
      ∃ result : Live.Enlargement collection,
        Live.Request.gather? staged ([] : Live.Request registry) = some collection ∧
        collection.enlarge? = some result ∧
        ∃ read : result.collection.shared.input.context.Value → ℝ,
          ∃ domain : result.collection.shared.input.context.Value → Prop,
            Transport.Closed read domain ∧ domain (result.previous.value (collection.shared.input.value coefficient)) ∧
            read (result.previous.value (collection.shared.input.value coefficient)) =
              liouvilleNumber 2 ∧
            domain result.parameter ∧ 0 < read result.parameter := by
  classical
  let request : Live.Request registry := []
  obtain ⟨collection, gathered, ⟨model⟩⟩ := Live.Request.gather?_models following
    reference.model request (by simp [request, Live.Request.owners])
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  obtain ⟨result, produced, _⟩ := collection.enlarge?_models model ambient
  obtain ⟨read, domain, data⟩ :=
    result.realize following gathered produced []
  have closed := data.closed
  have fixed := data.previousBaseFixed
  have parameter := data.parameter
  have positive := data.positive
  have preserved := fixed coefficient (liouvilleNumber 2) coefficient_value
  exact ⟨collection, result, gathered, produced, read, domain, closed,
    preserved.1, preserved.2, parameter, positive⟩

/-- Two successful enlargements preserve the registered coefficient along
both returned predecessor maps. No caller-supplied semantic equality is needed. -/
theorem shared_twice_realized :
    ∃ collection : Live.Collection staged ([] : Live.Request registry),
      ∃ first : Live.Enlargement collection,
        ∃ next : Live.Enlargement first.collection,
          Live.Request.gather? staged ([] : Live.Request registry) = some collection ∧
          collection.enlarge? = some first ∧ first.collection.enlarge? = some next ∧
          ∃ read : next.collection.shared.input.context.Value → ℝ,
            ∃ domain : next.collection.shared.input.context.Value → Prop,
              Transport.Closed read domain ∧ domain (next.previous.value
                (first.previous.value (collection.shared.input.value coefficient))) ∧
              read (next.previous.value
                (first.previous.value (collection.shared.input.value coefficient))) =
                liouvilleNumber 2 ∧
              domain next.parameter ∧ 0 < read next.parameter := by
  classical
  let request : Live.Request registry := []
  obtain ⟨collection, gathered, _⟩ := Live.Request.gather?_models following
    reference.model request (by simp [request, Live.Request.owners])
  let initial := collection.model following reference.model gathered
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  obtain ⟨first, built, _⟩ := collection.enlarge?_models initial ambient
  let previous := first.model initial ambient built
  let nextAmbient := Ambient.ofField (Hex.RationalFn ambient.Carrier)
  obtain ⟨next, produced, _⟩ := first.collection.enlarge?_models previous nextAmbient
  obtain ⟨read, domain, data⟩ :=
    next.realize_model previous produced []
  have closed := data.closed
  have fixed := data.representativeFixed
  have parameter := data.parameter
  have positive := data.positive
  let inherited := Context.baseValue staged.infinitesimal
    (RationalFn.C (Context.baseStored staged coefficient))
  have real : PackedContext.Realization.RealValue following.infinitesimal inherited
      (liouvilleNumber 2) :=
    (PackedContext.Realization.realValue_infinitesimal following coefficient _).mpr coefficient_value
  have preserved := fixed inherited (liouvilleNumber 2) real
    (first.previous.value (collection.shared.input.value coefficient))
    (first.model_constant initial ambient built coefficient)
  exact ⟨collection, first, next, gathered, built, produced, read, domain, closed,
    preserved.1, preserved.2, parameter, positive⟩

/-- A nonempty owner with an actual producer-built algebraic suffix keeps its
registered coefficient when gathered into the common target. The prescribed
value is read through the returned owner inclusion. -/
theorem shared_owner_realized :
    ∃ descriptor : SignDet.Descriptor initial.Value Signature initial.sign initial.signature,
      ∃ roots,
        SignDet.Descriptor.buildRoots initial.sign initial.signature head .negInf .posInf =
          .ok (some roots) ∧ descriptor ∈ roots ∧
        let suffix : Suffix initial := .root descriptor .nil
        ∃ shared : Shared staged.infinitesimal [suffix.context],
          Shared.gather? staged.infinitesimal [suffix.context] = some shared ∧
          ∃ read : shared.input.context.Value → ℝ,
            ∃ domain : shared.input.context.Value → Prop,
              Transport.Closed read domain ∧ domain (shared.value ⟨0, by simp⟩ (suffix.embed coefficient)) ∧
              read (shared.value ⟨0, by simp⟩ (suffix.embed coefficient)) = liouvilleNumber 2 := by
  classical
  obtain ⟨roots, built, nonempty⟩ := producer
  obtain ⟨descriptor, member⟩ := List.exists_mem_of_ne_nil roots nonempty
  let suffix : Suffix initial := .root descriptor .nil
  have baseOrigin (base : PackedContext registry) : (Context.ofBase base).origin.base = base := by
    cases base with
    | pack base => change (Context.base base).origin.base = PackedContext.pack base; rw [Context.origin_base]; rfl
  have baseEq : suffix.context.origin.base = staged := by
    rw [Suffix.base_eq]
    exact baseOrigin staged
  obtain ⟨shared, gathered, _⟩ := Shared.gather?_models following.infinitesimal following.infinitesimal.reference.model
    [suffix.context]
    (by intro owner member; cases List.mem_singleton.mp member
        simp only [baseEq, PackedContext.infinitesimal_signature]
        exact ⟨List.Sublist.refl _, Nat.le_succ _⟩)
  obtain ⟨read, domain, data⟩ :=
    shared.realize_values following.infinitesimal gathered (fun _ => [])
  have closed := data.closed
  have ownerFixed := data.ownerFixed
  obtain ⟨ownerHistory, inherited⟩ := suffix.realValue_owner staged following
    coefficient (liouvilleNumber 2) coefficient_value
  have fixed := ownerFixed ⟨0, by simp⟩ ownerHistory (suffix.embed coefficient)
    (liouvilleNumber 2) inherited
  exact ⟨descriptor, roots, built, member, shared, gathered, read, domain, closed, fixed⟩

/-- Three actual predecessor maps retain the provider coefficient and a
fresh cross-term sign under one closed ordinary reader. -/
theorem shared_thrice_realized :
    ∃ collection : Live.Collection staged ([] : Live.Request registry),
      ∃ first : Live.Enlargement collection,
        ∃ second : Live.Enlargement first.collection,
          ∃ third : Live.Enlargement second.collection,
            Live.Request.gather? staged ([] : Live.Request registry) = some collection ∧
            collection.enlarge? = some first ∧ first.collection.enlarge? = some second ∧
            second.collection.enlarge? = some third ∧
            ∃ read : third.collection.shared.input.context.Value → ℝ,
              ∃ domain : third.collection.shared.input.context.Value → Prop,
                Transport.Closed read domain ∧
                let carried := third.previous.value (second.previous.value
                  (first.previous.value (collection.shared.input.value coefficient)))
                domain carried ∧ read carried = liouvilleNumber 2 ∧
                domain third.parameter ∧ 0 < read third.parameter ∧
                (SignType.sign (liouvilleNumber 2 - read third.parameter) : Int) =
                  third.collection.shared.input.context.sign (carried - third.parameter) := by
  classical
  let request : Live.Request registry := []
  obtain ⟨collection, gathered, _⟩ := Live.Request.gather?_models following
    reference.model request (by simp [request, Live.Request.owners])
  let initial := collection.model following reference.model gathered
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  obtain ⟨first, built, _⟩ := collection.enlarge?_models initial ambient
  let firstModel := first.model initial ambient built
  let nextAmbient := Ambient.ofField (Hex.RationalFn ambient.Carrier)
  obtain ⟨second, produced, _⟩ := first.collection.enlarge?_models firstModel nextAmbient
  let secondModel := second.model firstModel nextAmbient produced
  let finalAmbient := Ambient.ofField (Hex.RationalFn nextAmbient.Carrier)
  obtain ⟨third, final, _⟩ := second.collection.enlarge?_models secondModel finalAmbient
  let old := second.previous.value (first.previous.value (collection.shared.input.value coefficient))
  let carried := third.previous.value old
  obtain ⟨read, domain, data⟩ :=
    third.realize_model secondModel final [] [carried - third.parameter]
  have closed := data.closed
  have fresh := data.additional
  have fixed := data.representativeFixed
  have parameter := data.parameter
  have positive := data.positive
  let inherited := Context.baseValue staged.infinitesimal
    (RationalFn.C (Context.baseStored staged coefficient))
  let twice := Context.baseValue staged.infinitesimal.infinitesimal
    (RationalFn.C (Context.baseStored staged.infinitesimal inherited))
  obtain ⟨realFirst, sameFirst⟩ := first.realValue_step initial ambient built coefficient
    (liouvilleNumber 2) coefficient_value (collection.shared.input.value coefficient)
    (initial.input coefficient)
  obtain ⟨realSecond, sameSecond⟩ := second.realValue_step firstModel nextAmbient produced inherited
    (liouvilleNumber 2) realFirst (first.previous.value (collection.shared.input.value coefficient))
    sameFirst
  have preserved := fixed twice (liouvilleNumber 2) realSecond old sameSecond
  have difference := fresh (carried - third.parameter) (by simp)
  refine ⟨collection, first, second, third, gathered, built, produced, final,
    read, domain, closed, preserved.1, preserved.2, parameter, positive, ?_⟩
  rw [← preserved.2, ← closed.read_sub _ _ preserved.1 parameter]
  exact difference.2.1

/-- An actual nonempty frame requests both a provider coefficient and a
polynomial over a shorter owner base. Gathering into a deeper base and then
enlarging preserve the owner's inventory signs and every prescribed constant
under the same closed positive-parameter reader. -/
theorem enlarged_owner_realized :
    ∃ descriptor : SignDet.Descriptor initial.Value Signature initial.sign initial.signature,
      ∃ roots,
        SignDet.Descriptor.buildRoots initial.sign initial.signature head .negInf .posInf =
          .ok (some roots) ∧ descriptor ∈ roots ∧
        let suffix : Suffix initial := .root descriptor .nil
        let request : Live.Request registry := [⟨suffix.context,
          { values := [suffix.embed coefficient],
            polynomials := [DensePoly.C (suffix.embed coefficient)] }⟩]
        ∃ collection : Live.Collection staged.infinitesimal request,
          ∃ result : Live.Enlargement collection,
            request.gather? staged.infinitesimal = some collection ∧
            collection.enlarge? = some result ∧
            ∃ read : result.collection.shared.input.context.Value → ℝ,
              ∃ domain : result.collection.shared.input.context.Value → Prop,
                Transport.Closed read domain ∧
                (∀ index a, a ∈ request.inventory index →
                  domain (result.collection.shared.value index a) ∧
                  (SignType.sign (read (result.collection.shared.value index a)) : Int) =
                    (request.owners[index]).sign a) ∧
                (∀ index (original : (request.owners[index]).origin.base.Realization) a r,
                  (request.owners[index]).origin.RealValue original a r →
                  domain (result.collection.shared.value index a) ∧
                  read (result.collection.shared.value index a) = r) ∧
                domain (result.collection.shared.value ⟨0, by simp [request, Live.Request.owners]⟩
                  (suffix.embed coefficient)) ∧
                read (result.collection.shared.value ⟨0, by simp [request, Live.Request.owners]⟩
                  (suffix.embed coefficient)) = liouvilleNumber 2 ∧
                (SignType.sign (read (result.collection.shared.value
                  ⟨0, by simp [request, Live.Request.owners]⟩ (suffix.embed coefficient))) : Int) =
                  suffix.context.sign (suffix.embed coefficient) ∧
                domain result.parameter ∧ 0 < read result.parameter := by
  classical
  obtain ⟨roots, built, nonempty⟩ := producer
  obtain ⟨descriptor, member⟩ := List.exists_mem_of_ne_nil roots nonempty
  let suffix : Suffix initial := .root descriptor .nil
  let request : Live.Request registry := [⟨suffix.context,
    { values := [suffix.embed coefficient],
      polynomials := [DensePoly.C (suffix.embed coefficient)] }⟩]
  have baseOrigin (base : PackedContext registry) : (Context.ofBase base).origin.base = base := by
    cases base with
    | pack base =>
      change (Context.base base).origin.base = PackedContext.pack base
      rw [Context.origin_base]
      rfl
  have baseEq : suffix.context.origin.base = staged := by
    rw [Suffix.base_eq]
    exact baseOrigin staged
  obtain ⟨collection, gathered, ⟨model⟩⟩ := Live.Request.gather?_models following.infinitesimal
    following.infinitesimal.reference.model request (by
      intro owner member
      have same : owner = suffix.context := by simpa [request, Live.Request.owners] using member
      subst owner
      simp only [baseEq, PackedContext.infinitesimal_signature]
      exact ⟨List.Sublist.refl _, Nat.le_succ _⟩)
  let ambient := Ambient.ofField (Hex.RationalFn following.infinitesimal.reference.Carrier)
  obtain ⟨result, produced, _⟩ := collection.enlarge?_models model ambient
  obtain ⟨read, domain, data⟩ :=
    result.realize following.infinitesimal gathered produced []
  have closed := data.closed
  have finite := data.finite
  have ownerFixed := data.ownerFixed
  have parameter := data.parameter
  have positive := data.positive
  let index : Fin request.owners.length := ⟨0, by simp [request, Live.Request.owners]⟩
  obtain ⟨ownerHistory, inherited⟩ := suffix.realValue_owner staged following
    coefficient (liouvilleNumber 2) coefficient_value
  have preserved := ownerFixed index ownerHistory (suffix.embed coefficient)
    (liouvilleNumber 2) inherited
  have requested : suffix.embed coefficient ∈ request.inventory index := by
    simp only [request, index, Live.Request.inventory, Live.Frame.inventory,
      Live.Request.frame, Live.Request.owners]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
  have sign := (finite index (suffix.embed coefficient) requested).2.1
  exact ⟨descriptor, roots, built, member, collection, result, gathered, produced,
    read, domain, closed, fun index a member =>
      ⟨(finite index a member).1, (finite index a member).2.1⟩,
    ownerFixed, preserved.1, preserved.2, sign, parameter, positive⟩

end Hex.RealClosure.Tower.RegisteredRealizationTests

/-- info: '_private.HexRealClosureTheory.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.realized

/-- info: '_private.HexRealClosureTheory.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.shared_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.shared_realized

/-- info: '_private.HexRealClosureTheory.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.shared_twice_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.shared_twice_realized

/-- info: '_private.HexRealClosureTheory.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.shared_owner_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.shared_owner_realized

/-- info: '_private.HexRealClosureTheory.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.shared_thrice_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.shared_thrice_realized

/-- info: '_private.HexRealClosureTheory.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.enlarged_owner_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.enlarged_owner_realized
