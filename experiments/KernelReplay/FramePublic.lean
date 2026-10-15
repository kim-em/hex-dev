/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FrameOwners
public import KernelReplay.FrameOperand

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.FramePublic

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
local instance : Field (Hex.RationalFn (Hex.RationalFn Rat)) := HexPolyTheory.fieldOfGrind

noncomputable def firstReader
    (interpretation : Hex.RealClosure.CoefficientMap (Hex.RationalFn (Hex.RationalFn Rat)) Real)
    (alpha : Real) (value : Element FrameOwners.first) : Real :=
  Packing.eval (FiniteBaseProbe.base.partialRead interpretation) alpha value.polynomial

noncomputable def secondReader
    (interpretation : Hex.RealClosure.CoefficientMap (Hex.RationalFn (Hex.RationalFn Rat)) Real)
    (alpha beta : Real) (value : Element FrameOwners.second) : Real :=
  Packing.eval (firstReader interpretation alpha) beta value.polynomial

noncomputable def nativeSquare
    (interpretation : Hex.RealClosure.CoefficientMap (Hex.RationalFn (Hex.RationalFn Rat)) Real)
    (alpha beta : Real) : Real :=
  secondReader interpretation alpha beta (FrameOwners.beta * FrameOwners.beta)

/-- The finite product at index zero concerns the original computed generator.
The supplied reader, interpretation and two coordinates are kept fixed. -/
theorem product
    (interpretation : Hex.RealClosure.CoefficientMap (Hex.RationalFn (Hex.RationalFn Rat)) Real)
    (alpha beta : Real)
    (data : Hex.RealClosure.Transport.Product (secondReader interpretation alpha beta)
      FrameOperand.requestPoly FrameOperand.requestPoly) :
    nativeSquare interpretation alpha beta =
      secondReader interpretation alpha beta FrameOwners.beta *
        secondReader interpretation alpha beta FrameOwners.beta := by
  let read := secondReader interpretation alpha beta
  let predicate (value : Element FrameOwners.second) : Prop :=
    read (value * value) = read value * read value
  have checked := data.products 0 FrameOperand.request_bound 0 FrameOperand.request_bound
  exact Eq.mp (congrArg predicate FrameOperand.request_coeff) checked

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FramePublic.product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms product

end Hex.RealClosure.Algebraic.KernelReplay.FramePublic
