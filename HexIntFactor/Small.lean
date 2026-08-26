/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Partial
public import HexPrimality.Search

public section

/-! Structural reductions and trial division.  These routines are untrusted
search producers: their output is consumed only after `checkPartial`. -/

namespace Hex

namespace Nat

/-- Remove at most `fuel` copies of `p` from `n`. -/
def removePower (p n : Nat) : Nat → Nat × Nat
  | 0 => (0, n)
  | fuel + 1 =>
      if 1 < p ∧ n % p = 0 then
        let out := removePower p (n / p) fuel
        (out.1 + 1, out.2)
      else (0, n)

/-- Number of trailing zero bits, together with the odd cofactor. -/
def splitTwos (n : Nat) : Nat × Nat := removePower 2 n (n.log2 + 1)

private def trialGo : List Nat → Nat → List PrimePower × Nat
  | [], n => ([], n)
  | p :: ps, n =>
      if n = 1 then ([], 1)
      else
        let removed := removePower p n (n.log2 + 1)
        let rest := trialGo ps removed.2
        if removed.1 = 0 then rest
        else (⟨removed.1, .small p⟩ :: rest.1, rest.2)

/-- Trial division against the complete committed primality table. -/
def trialFactors (n : Nat) : List PrimePower × Nat :=
  trialGo primeTable.toList n

private def rootGo (n k : Nat) : Nat → Nat → Nat → Option Nat
  | 0, lo, _ =>
      match boundedPowMul n lo 1 k with
      | some v => if v = n then some lo else none
      | none => none
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then
        match boundedPowMul n lo 1 k with
        | some v => if v = n then some lo else none
        | none => none
      else
        let mid := (lo + hi) / 2
        match boundedPowMul n mid 1 k with
        | none => rootGo n k fuel lo mid
        | some v =>
            if v = n then some mid
            else if v < n then rootGo n k fuel mid hi
            else rootGo n k fuel lo mid

/-- Exact positive `k`th root, found by bounded binary search. -/
def exactRoot? (n k : Nat) : Option Nat :=
  if k < 2 then none
  else rootGo n k (n.log2 + 2) 1 (n + 1)

private def perfectPowerGo (n maxExponent : Nat) : List Nat → Option (Nat × Nat)
  | [] => none
  | k :: ks =>
      if maxExponent < k then none
      else
        match exactRoot? n k with
        | some base => if 1 < base then some (base, k) else none
        | none => perfectPowerGo n maxExponent ks

/-- Detect `n = base^exponent` with prime `exponent ≥ 2`.  Trying only prime
exponents is complete for perfect powers. -/
def perfectPower? (n : Nat) : Option (Nat × Nat) :=
  if n < 4 then none
  else perfectPowerGo n n.log2 primeTable.toList

/-- Which structural producer made a small-route candidate. -/
inductive SmallRoute where
  | trial
  | perfectPower
deriving Repr, DecidableEq

/-- Trial-produced prime powers plus a possibly powered residual.  The
`residualBase`/`residualExponent` split lets the caller certify a large prime
base after perfect-power reduction and then restore its multiplicity. -/
structure SmallCandidate where
  factors : List PrimePower
  residualBase : Nat
  residualExponent : Nat
  route : SmallRoute
deriving Repr

/-- Apply perfect-power reduction before table trial division. -/
def smallCandidate (n : Nat) : SmallCandidate :=
  match perfectPower? n with
  | some (base, exponent) =>
      let out := trialFactors base
      { factors := out.1.map fun e => { e with exponent := e.exponent * exponent }
        residualBase := out.2
        residualExponent := exponent
        route := .perfectPower }
  | none =>
      let out := trialFactors n
      { factors := out.1
        residualBase := out.2
        residualExponent := 1
        route := .trial }

end Nat

end Hex
