/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.PackingReplay
import all HexRealClosureMathlib.Packing

public section

namespace Hex.RealClosure.Algebraic
open Hex.SignDet HexPolyMathlib.Interpret

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Read each stored polynomial at the level's one selected point. Its finite
operation laws come from original packing records, rather than global closure. -/
@[expose] noncomputable def Context.finiteRead (context : Context E Ctx coeffSign parent)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (data : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence) :
    Element context → K :=
  fun a => Packing.eval read (context.finitePoint read zero unit data) a.polynomial

/-- The stored zero has the required value without any packing lookup. -/
theorem Context.finiteRead_zero (context : Context E Ctx coeffSign parent)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (data : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence) :
    context.finiteRead read zero unit data 0 = 0 := by
  unfold finiteRead
  rw [Element.polynomial_zero]
  have mapped : Transport.polynomial read (0 : Hex.DensePoly E) = 0 :=
    (Transport.polynomial_zero read zero 0 (by simp)).mpr rfl
  simp [Packing.eval, mapped]

/-- The unit equation is derived from the exact unit key retained by native
replay. Its value is never assumed for the new coefficient reader. -/
theorem Context.finiteRead_one (context : Context E Ctx coeffSign parent)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (entries : List (Packing context))
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (key : (Packing.find entries 1).isSome = true) :
    context.finiteRead read zero unit descriptorData 1 = 1 := by
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp key
  exact Packing.eval_one entry (Packing.find_native entries _ found).1 read zero unit _
    (entry.atPoint read zero unit descriptorData
      (packingData entry (Packing.find_mem entries _ found))).1

/-- A reached natural cast is derived from its retained constant-polynomial
key and the predecessor's cast law. The collector must retain these keys for
every derivative degree reached at later levels. -/
theorem Context.finiteRead_natCast (context : Context E Ctx coeffSign parent)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (entries : List (Packing context))
    (packingData : ∀ entry ∈ entries, Packing.Data entry read)
    (n : Nat) (cast : read (n : E) = (n : K))
    (key : (Packing.find entries (DensePoly.C (n : E))).isSome = true) :
    context.finiteRead read zero unit descriptorData (n : Element context) = (n : K) := by
  obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp key
  exact Packing.eval_nat entry n (Packing.find_native entries _ found).1 read zero cast _
    (entry.atPoint read zero unit descriptorData
      (packingData entry (Packing.find_mem entries _ found))).1

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Context.finiteRead_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.finiteRead_zero

/-- info: 'Hex.RealClosure.Algebraic.Context.finiteRead_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.finiteRead_one

/-- info: 'Hex.RealClosure.Algebraic.Context.finiteRead_natCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.finiteRead_natCast
