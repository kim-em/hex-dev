/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.LiveRequest

public section

namespace Hex.RealClosure.Tower.Live

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
    {request : Request registry} (original : Collection base request)
    (following : base.Realization) (reference : Model (Context.ofBase base) K)
    (gathered : request.gather? base = some original)
    (ambient : Ambient (Hex.RationalFn K)) (first : Enlargement original)
    (firstProduced : original.enlarge? = some first)
    (nextAmbient : Ambient (Hex.RationalFn ambient.Carrier)) (twice : Enlargement first.collection)
    (twiceProduced : first.collection.enlarge? = some twice) :
    let initial := original.model following reference gathered
    let once := first.model initial ambient firstProduced
    let returned := (twice.model once nextAmbient twiceProduced).target
    let inclusion := (Ambient.coefficientHom nextAmbient).comp (Ambient.coefficientHom ambient)
    List.Forall₂ (fun frame refreshed =>
      refreshed.values.map returned.value = frame.values.map (fun v => inclusion (initial.target.value v)) ∧
      refreshed.polynomials.map (HexPolyMathlib.Interpret.interpret returned.value returned.zero_iff) =
        frame.polynomials.map (fun p =>
          (HexPolyMathlib.Interpret.interpret initial.target.value initial.target.zero_iff p).map inclusion) ∧
      refreshed.descriptors.map (selectedValue returned) =
        frame.descriptors.map (fun d => inclusion (selectedValue initial.target d)))
      original.frames twice.collection.frames :=
  original.preserve_twice following reference gathered ambient first firstProduced nextAmbient twice twiceProduced

end Hex.RealClosure.Tower.Live

/-- info: 'Hex.RealClosure.Tower.Live.preserve_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.preserve_frames
