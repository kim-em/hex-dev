/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SharedRealization

public section

open scoped List

namespace Hex.RealClosure.Tower.Live.RealizationTests

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {request : Request registry} {original : Collection base request}

/-- Public callers obtain one positive real parameter and simultaneous old
sum/product signs after actual enlargement. No model, ambient field, separate
owner reader, or arithmetic agreement is supplied. The old native context may
contain any stored algebraic suffix over any number of infinitesimal stages. -/
theorem enlarge_arithmetic (result : Enlargement original) (following : base.Realization)
    (gathered : request.gather? base = some original)
    (produced : original.enlarge? = some result)
    (a b : original.shared.input.context.Value) :
    ∃ x y epsilon : ℝ, 0 < epsilon ∧
      (SignType.sign x : Int) = original.shared.input.context.sign a ∧
      (SignType.sign y : Int) = original.shared.input.context.sign b ∧
      (SignType.sign (x + y) : Int) = original.shared.input.context.sign (a + b) ∧
      (SignType.sign (x * y) : Int) = original.shared.input.context.sign (a * b) := by
  obtain ⟨read, domain, _, closed, finite, _, _, positive⟩ :=
    result.realize following gathered produced [a, b, a + b, a * b]
  have left := finite a (by simp)
  have right := finite b (by simp)
  have sum := finite (a + b) (by simp)
  have product := finite (a * b) (by simp)
  refine ⟨read (result.previous.value a), read (result.previous.value b),
    read result.parameter, positive, left.2, right.2, ?_, ?_⟩
  · rw [← closed.read_add a b left.1 right.1]
    exact sum.2
  · rw [← closed.read_mul a b left.1 right.1]
    exact product.2

end Hex.RealClosure.Tower.Live.RealizationTests

/-- info: 'Hex.RealClosure.Tower.Live.RealizationTests.enlarge_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.RealizationTests.enlarge_arithmetic
