/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModular.SymMod
public import HexMvGcd.Fast

@[expose] public section

/-! Bounded route-2 proposal and concrete coefficient backends. -/

namespace Hex.MvPoly

universe u

/-- A conservative projected-size bound for the Kronecker route. -/
def heuristicProjectedBits {n : Nat}
    (degrees : Mono n) (coefficientBits : Nat) : Nat :=
  coefficientBits * (List.finRange n).foldl
    (fun acc i => acc * (degrees[i] + 1)) 1

/-- Mixed-radix stride of variable `i`. -/
def heuristicStride {n : Nat} (degrees : Mono n) (i : Fin n) : Nat :=
  (List.finRange n).foldl
    (fun stride j =>
      if j.val < i.val then stride * (degrees[j] + 1) else stride) 1

/-- Number of collision-free mixed-radix coefficient slots. -/
def heuristicSlots {n : Nat} (degrees : Mono n) : Nat :=
  (List.finRange n).foldl (fun slots i => slots * (degrees[i] + 1)) 1

/-- Decode a Kronecker digit position back to its exponent vector. -/
def heuristicDecode {n : Nat} (degrees : Mono n) (index : Nat) : Mono n :=
  Hex.Vector.ofFn' fun i =>
    index / heuristicStride degrees i % (degrees[i] + 1)

/-- Symmetric base digits, low digit first and explicitly fuel bounded. -/
def heuristicDigits (base : Nat) : Int → Nat → List Int
  | _, 0 => []
  | value, fuel + 1 =>
      if value = 0 then []
      else
        let digit := Modular.symMod value base
        digit :: heuristicDigits base ((value - digit) / Int.ofNat base) fuel

/-- Largest absolute input coefficient. -/
def heuristicCoeffNorm {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (p : MvPoly n Int cmp) : Nat :=
  p.termsList.foldl (fun bound term => max bound term.2.natAbs) 0

/-- Collision-free mixed-radix evaluation. -/
def heuristicEval {n : Nat} {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (degrees : Mono n) (base : Nat) (p : MvPoly n Int cmp) : Int :=
  eval (fun i => Int.ofNat base ^ heuristicStride degrees i) p

/-- Reconstruct a sparse integer polynomial from symmetric Kronecker digits.
Positions beyond the mixed-radix box are ignored. -/
def heuristicReconstruct {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [IsMonomialOrder cmp] (degrees : Mono n) (base : Nat)
    (value : Int) : MvPoly n Int cmp :=
  let slots := heuristicSlots degrees
  let digits := heuristicDigits base value (slots + 1)
  ofTerms <| (List.range (min slots digits.length)).map fun index =>
    (heuristicDecode degrees index, digits.getD index 0)

/-- One genuine GCDHEU candidate over integers.  Accidental factors in the
evaluated cofactors remain possible and are intentionally left for
`checkedCandidate?` to reject. -/
def intHeuristicCandidateAt {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly n Int cmp) (base : Nat) : MvPoly n Int cmp :=
  let fPrimitive := primPart f
  let hPrimitive := primPart h
  let degrees := Mono.lcm fPrimitive.degrees hPrimitive.degrees
  let fValue := heuristicEval degrees base fPrimitive
  let hValue := heuristicEval degrees base hPrimitive
  let value : Int := Int.ofNat (Int.gcd fValue hValue)
  let raw := heuristicReconstruct (cmp := cmp) degrees base value
  let commonContent := GcdOps.gcd (content f) (content h)
  polyNormalize (C commonContent * primPart raw)

/-- Projected bit cost of one mixed-radix evaluation. -/
def intHeuristicCost {n : Nat}
    {cmp : Mono n → Mono n → Ordering}
    [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
    (f h : MvPoly n Int cmp) (base : Nat) : Nat :=
  let degrees := Mono.lcm f.degrees h.degrees
  let coeffBits := Nat.log2
    (max 2 (max (heuristicCoeffNorm f) (heuristicCoeffNorm h))) + 1
  coeffBits + heuristicSlots degrees * (Nat.log2 (max 2 base) + 1)

/-- Retry GCDHEU while charging every growing evaluation against the caller's
projected-bit budget. -/
def intHeuristicLoop {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (f h : MvPoly n Int cmp) : Nat → Nat → Option (GcdCert n Int cmp)
  | _, 0 => none
  | base, remaining + 1 =>
      let cost := intHeuristicCost f h base
      if cost > remaining + 1 then none
      else
        match checkedCandidate? f h (intHeuristicCandidateAt f h base) with
        | some cert => some cert
        | none =>
            intHeuristicLoop f h (2 * base + 1)
              (remaining + 1 - max 1 cost)
termination_by _ remaining => remaining
decreasing_by
  omega

/-- Route 2 over integers. -/
def intHeuristicCert? {n : Nat}
    {cmp : Mono n → Mono n → Ordering} [IsMonomialOrder cmp]
    (cfg : GcdConfig) (f h : MvPoly n Int cmp) :
    Option (GcdCert n Int cmp) :=
  let norm := max (heuristicCoeffNorm f) (heuristicCoeffNorm h)
  let base := max 3 (2 * norm + 1)
  intHeuristicLoop f h base cfg.heuristicBitBudget

instance fpPolyProducer {p : Nat} [hp : ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] : GcdProducer (@FpPoly p hp) where
  propose := fun cmp _ cfg f h => fpFastProposal cmp cfg f h

end Hex.MvPoly
