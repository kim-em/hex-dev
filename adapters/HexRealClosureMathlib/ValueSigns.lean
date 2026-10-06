/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ValueSigns
public import HexRealClosureMathlib.Packing
import all HexRealClosureMathlib.Packing

public section

namespace Hex.RealClosure.Algebraic.ValueSign
open Hex.SignDet HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K]

/-- A stored-value replay proves its cached input tag at the selected point.
No packing, reduction or whole-field interpretation law is assumed. -/
theorem eval_sign (record : ValueSign context) (read : E → K) (x : K)
    (observed : signsAt (fun y : K => y) (fun _ => Iff.rfl)
      ([record.value.polynomial].map (Transport.polynomial read)) x = [record.value.sign]) :
    (SignType.sign (Packing.eval read x record.value.polynomial) : Int) = record.value.sign := by
  simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true,
    Packing.eval] using observed

/-- Only the actual stored polynomial's joint descriptor/query replay is
required from the predecessor; input signs have a distinct evidence boundary. -/
structure Data (record : ValueSign context) (read : E → K) : Prop where
  replay : Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
    context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++ [record.value.polynomial]) record.signs.evidence

end Hex.RealClosure.Algebraic.ValueSign

/-- info: 'Hex.RealClosure.Algebraic.ValueSign.eval_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.ValueSign.eval_sign
