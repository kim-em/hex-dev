/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts

public section

namespace Hex.RealClosure.Algebraic.LowerProbe

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- Horner evaluation of stored representatives, reducing each partial sum
with the existing context policy. No intermediate algebraic element is packed. -/
@[expose] def evalCoefficients (cs : List (Element context)) (x : Element context) :
    DensePoly E :=
  cs.foldr (fun c acc => context.reduce (acc * x.polynomial + c.polynomial)) 0

/-- The same Horner order as the shared evaluation, with ordinary polynomial
operations and context reduction after each step. The result's sign still
requires supplied lower-level evidence. -/
@[expose] def evalPolynomial (p : DensePoly (Element context)) (x : Element context) :
    DensePoly E :=
  evalCoefficients p.toArray.toList x

/-- Read the final sign from an already checked lower-level graph. Neither
the interpretation laws nor a scalar sign producer are executable arguments. -/
@[expose] def readEvalSign? (p : DensePoly (Element context)) (x : Element context)
    (claimed : Int) {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Hex.SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option Int :=
  (context.readSigns? (evalPolynomial p x) claimed memo index).map (·.value)

/-- Check a scalar difference before packing it into an algebraic value.
A claimed zero establishes a semantic identity through lower-level replay. -/
@[expose] def readDifferenceSign? (a b : Element context) (claimed : Int)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Hex.SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option Int :=
  (context.readSigns? (a.polynomial - b.polynomial) claimed memo index).map (·.value)

theorem readEvalSign_value (p : DensePoly (Element context)) (x : Element context)
    (claimed : Int) {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Hex.SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    (value : Int) (h : readEvalSign? p x claimed memo index = some value) : value = claimed := by
  unfold readEvalSign? at h
  cases hs : context.readSigns? (evalPolynomial p x) claimed memo index with
  | none => simp [hs] at h
  | some signs =>
    have hv := Context.readSigns_value hs
    simpa [hs, hv] using h.symm

end Hex.RealClosure.Algebraic.LowerProbe
