/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.FrameFormat

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} (parent : Context registry)
variable (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)

/-- Read the actual stored representative at this native root level.
General representatives have no degree bound. -/
@[expose] def Context.polynomial : (parent.adjoin descriptor).context.Value → DensePoly parent.Value := by
  cases parent with
  | pack chain =>
    have h := (Context.adjoin_native chain descriptor).1
    exact fun value => Algebraic.Element.polynomial
      (_root_.cast (congrArg Context.Value h) value)

/-- Pack a predecessor-coefficient polynomial in the actual public child.
Partial application retains the native target context for repeated packing. -/
@[expose] def Context.ofPoly : DensePoly parent.Value → (parent.adjoin descriptor).context.Value := by
  cases parent with
  | pack chain =>
    have h := (Context.adjoin_native chain descriptor).1
    let native := Algebraic.Context.adjoin descriptor (Context.pack chain).isClean
    exact fun p => _root_.cast (congrArg Context.Value h.symm)
      (Algebraic.Element.ofPoly (context := native) p)

end Hex.RealClosure.Tower
