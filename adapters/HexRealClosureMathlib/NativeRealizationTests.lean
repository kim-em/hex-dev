/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.NativeRealization
public import HexRealClosure.TowerEnlarge
public import HexOrderedFnMathlib.LiouvilleTests

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

open BaseContext OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private def key : ConstantKey := ⟨"liouville", 1⟩
private def registry : Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none
private theorem present : (registry key).isSome = true := by simp [registry, key]
private noncomputable abbrev rational := RealPrefix.Model.rational registry

private theorem transcendence :
    letI : Field rational.context.Carrier := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence rational.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyMathlib.fieldOfGrind
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
  have polynomial : HexPolyMathlib.Interpret.interpret model.value model.zero_iff head =
      (Polynomial.X : Polynomial reference.Carrier) := by
    ext n
    by_cases equal : n = 1
    · simp [head, HexPolyMathlib.Interpret.coeff_interpret, DensePoly.coeff_monomial,
        Polynomial.coeff_X, equal, model.one]
    · simp only [head, HexPolyMathlib.Interpret.coeff_interpret, DensePoly.coeff_monomial,
        Polynomial.coeff_X, ite_eq_right equal, ite_eq_right (Ne.symm equal)]
      exact (model.zero_iff 0).mpr rfl
  have domain : HexSturmMathlib.Domain model.value model.zero_iff head .negInf .posInf := by
    rw [HexSturmMathlib.Domain, polynomial]
    exact ⟨Polynomial.X_ne_zero, Polynomial.irreducible_X.squarefree, trivial, trivial, trivial⟩
  obtain ⟨roots, built, cover, _, _⟩ := SignDet.Descriptor.buildRoots_roots
    model.value model.zero_iff model.one model.add model.sub model.mul model.nat
    model.sign model.neg model.inv initial.signature head .negInf .posInf domain
  have root : (0 : reference.Carrier) ∈ HexRealRootsMathlib.Tarski.rootsIn
      (HexPolyMathlib.Interpret.interpret model.value model.zero_iff head) .negInf .posInf := by
    rw [polynomial, HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ Polynomial.X_ne_zero]
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

end Hex.RealClosure.Tower.RegisteredRealizationTests

/-- info: '_private.HexRealClosureMathlib.NativeRealizationTests.0.Hex.RealClosure.Tower.RegisteredRealizationTests.realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.RegisteredRealizationTests.realized
