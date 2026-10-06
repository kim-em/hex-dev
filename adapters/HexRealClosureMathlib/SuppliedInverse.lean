/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.FinitePoint
public import HexRealClosureMathlib.InverseEquation
import all HexRealClosureMathlib.Packing

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet HexRealRootsMathlib

variable {E : Type u} {Ctx : Type v} {K : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent} {entry : Packing context}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Reached finite replay and arithmetic premises for a supplied inverse
equation. The packing equation is retained separately; neither premise says
that the supplied output is the native algorithm's literal candidate. -/
structure Inverse.Equation.Data (record : Inverse.Equation entry) (read : E → K) : Prop where
  packing : Packing.Data entry read
  replay : Transport.Finite.ReplayData read coeffSign (fun x : K => (SignType.sign x : Int))
    context.root.raw.head context.root.raw.lower context.root.raw.upper
    (context.root.raw.queries ++
      [record.argument.polynomial, record.argument.polynomial * entry.value.polynomial - 1])
    record.signs.evidence
  product : Transport.Product read record.argument.polynomial entry.value.polynomial
  difference : Transport.Difference read (record.argument.polynomial * entry.value.polynomial) 1

/-- The supplied output, operand and original packing equation hold at the
same finite selected point as every other inventory. -/
theorem Inverse.Equation.atPoint (record : Inverse.Equation entry)
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (descriptorData : Transport.Finite.DescriptorData read coeffSign
      (fun x : K => (SignType.sign x : Int)) context.root.raw context.root.evidence)
    (data : Inverse.Equation.Data record read) :
    let x := context.finitePoint read zero unit descriptorData
    eval read x entry.value.polynomial = eval read x entry.original ∧
      eval read x entry.value.polynomial = (eval read x record.argument.polynomial)⁻¹ ∧
      (SignType.sign (eval read x entry.original) : Int) = entry.value.sign ∧
      (SignType.sign (eval read x record.argument.polynomial) : Int) = record.argument.sign := by
  dsimp only
  have packing := entry.atPoint read zero unit descriptorData data.packing
  have observed := (Context.finitePoint_signs read zero unit descriptorData _ record.signs
    data.replay).trans record.observed
  have pair : (SignType.sign (eval read (context.finitePoint read zero unit descriptorData)
      record.argument.polynomial) : Int) = record.argument.sign ∧
      (SignType.sign (eval read (context.finitePoint read zero unit descriptorData)
        (record.argument.polynomial * entry.value.polynomial - 1)) : Int) = 0 := by
    simpa only [signsAt, List.map_cons, List.map_nil, List.cons.injEq, and_true, eval]
      using observed
  exact ⟨packing.1, record.eval_inv read zero unit _ data.product data.difference observed,
    packing.2, pair.1⟩

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.Equation.atPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.Equation.atPoint
