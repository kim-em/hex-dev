/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.LiveRequest

public section

namespace Hex.RealClosure.Tower.Live

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

end Hex.RealClosure.Tower.Live
