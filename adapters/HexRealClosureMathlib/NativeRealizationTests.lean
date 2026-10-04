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

private theorem originBase (base : PackedContext registry) :
    (Context.ofBase base).origin.base = base := by
  cases base with
  | pack base => simp only [Context.ofBase, Context.origin_base, Origin.base]; rfl

/-- One actual caller-certified Liouville prefix, its stored infinitesimal
extension and a native root adjunction feed the public ordinary reader API.
No additional sign, transport or ambient-model premises are supplied. -/
example (descriptor : SignDet.Descriptor initial.Value Signature initial.sign initial.signature)
    (a : (initial.adjoin descriptor).context.Value) :
    ∃ read : (initial.adjoin descriptor).context.Value → ℝ,
      ∃ domain : (initial.adjoin descriptor).context.Value → Prop,
        Transport.Closed read domain ∧ domain a ∧
          (SignType.sign (read a) : Int) = (initial.adjoin descriptor).context.sign a := by
  have same : (initial.adjoin descriptor).context.origin.base = staged := by
    rw [Context.origin_adjoin, Origin.snoc_base]
    exact originBase staged
  let history : (initial.adjoin descriptor).context.origin.base.Realization := same.symm ▸ following
  obtain ⟨read, domain, closed, finite, real⟩ :=
    (initial.adjoin descriptor).context.realize_values history [a]
  exact ⟨read, domain, closed, (finite a (by simp)).1, (finite a (by simp)).2⟩

end Hex.RealClosure.Tower.RegisteredRealizationTests
