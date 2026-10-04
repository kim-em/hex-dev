/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.NativeRealization
public import HexRealClosure.TowerEnlarge

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

end Hex.RealClosure.Tower.NativeRealizationTests
