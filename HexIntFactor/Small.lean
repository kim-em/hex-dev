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

/-- Number of trailing zero bits, together with the cofactor after one right
shift. Zero maps to `(0, 0)`; every positive input produces an odd cofactor. -/
def splitTwos (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else
    let exponent := (n ^^^ (n &&& (n - 1))).log2
    (exponent, n >>> exponent)

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
  if n = 0 then ([], 0) else trialGo primeTable.toList n

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
  else
    let rootBits := n.log2 / k + 1
    rootGo n k (rootBits + 2) 1 ((1 : Nat) <<< rootBits)

private def perfectPowerGo (n maxExponent : Nat) : List Nat → Option (Nat × Nat)
  | [] => none
  | k :: ks =>
      if maxExponent < k then none
      else
        match exactRoot? n k with
        | some base =>
            if 1 < base then some (base, k)
            else perfectPowerGo n maxExponent ks
        | none => perfectPowerGo n maxExponent ks

private def perfectPowerAboveTable (n : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | k + 1 =>
      if k + 1 < primeTableBound then none
      else if !isPrime (k + 1) then perfectPowerAboveTable n k
      else
        match exactRoot? n (k + 1) with
        | some base =>
            if 1 < base then some (base, k + 1)
            else perfectPowerAboveTable n k
        | none => perfectPowerAboveTable n k

/-- Detect `n = base^exponent` with `exponent ≥ 2`. The committed prime
exponents cover the table range; a descending scan covers every larger prime
exponent through `n.log2`. Testing prime exponents is complete because every
composite exponent has a prime divisor. -/
def perfectPower? (n : Nat) : Option (Nat × Nat) :=
  if n < 4 then none
  else
    match perfectPowerGo n n.log2 primeTable.toList with
    | some power => some power
    | none => perfectPowerAboveTable n n.log2

/-- Which structural producer made a small-route candidate. -/
inductive SmallRoute where
  | trial
  | twos
  | perfectPower
  | twosPower
deriving Repr, DecidableEq

/-- Trial-produced prime powers plus a possibly powered residual.  The
`residualBase`/`residualExponent` split lets the caller certify a large prime
base after perfect-power reduction and then restore its multiplicity. -/
structure SmallCandidate where
  /-- Prime powers completely removed by structural and table routes. -/
  factors : List PrimePower
  /-- Cofactor base still requiring primality or splitting work. -/
  residualBase : Nat
  /-- Multiplicity to restore after factoring `residualBase`. -/
  residualExponent : Nat
  /-- Structural route taken before returning the candidate. -/
  route : SmallRoute
deriving Repr

/-- Scale every multiplicity represented by a structural candidate. -/
def SmallCandidate.scale (candidate : SmallCandidate) (multiplier : Nat) :
    SmallCandidate :=
  { factors := candidate.factors.map fun entry =>
      { entry with exponent := entry.exponent * multiplier }
    residualBase := candidate.residualBase
    residualExponent := if candidate.residualBase = 1 then 1
      else candidate.residualExponent * multiplier
    route := candidate.route }

private def exponentGcd : List PrimePower → Nat
  | [] => 0
  | entry :: entries =>
      entries.foldl (fun common next => Nat.gcd common next.exponent)
        entry.exponent

/-- Apply table trial division and perfect-power reduction to an odd cofactor.
A complete table factorization exposes perfect powers directly through the gcd
of its multiplicities, avoiding a redundant root search on the dominant small
dispatch path while preserving the structural route classification. -/
private def oddCandidate (n : Nat) : SmallCandidate :=
  let out := trialFactors n
  if out.2 = 1 then
    let exponent := exponentGcd out.1
    if 1 < exponent then
      { factors := out.1
        residualBase := 1
        residualExponent := 1
        route := .perfectPower }
    else
      { factors := out.1
        residualBase := 1
        residualExponent := 1
        route := .trial }
  else
    match perfectPower? n with
    | some (base, exponent) =>
        let baseOut := trialFactors base
        { factors := baseOut.1.map fun e =>
            { e with exponent := e.exponent * exponent }
          residualBase := baseOut.2
          residualExponent := exponent
          route := .perfectPower }
    | none =>
        { factors := out.1
          residualBase := out.2
          residualExponent := 1
          route := .trial }

/-- Remove the full power of two, then apply perfect-power reduction and table
trial division to the odd cofactor. -/
def smallCandidate (n : Nat) : SmallCandidate :=
  let twos := splitTwos n
  if twos.1 = 0 then oddCandidate n
  else
    let odd := oddCandidate twos.2
    { factors := ⟨twos.1, .small 2⟩ :: odd.factors
      residualBase := odd.residualBase
      residualExponent := odd.residualExponent
      route := match odd.route with
        | .perfectPower => .twosPower
        | .trial => .twos
        -- `oddCandidate` currently returns only the preceding two routes.
        | .twos | .twosPower => .twos }

end Nat

end Hex
