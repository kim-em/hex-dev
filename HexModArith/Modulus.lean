/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Prime

public section

/-!
Bundled word-sized moduli and the runtime prime supply for `hex-mod-arith`.

The structures in this module carry the dependent `ZMod64.Bounds` evidence
needed to instantiate modular arithmetic at a modulus selected at runtime.
-/
namespace Hex

namespace ZMod64

/-- A usable word-sized modulus together with the evidence required by
`ZMod64`. -/
structure Modulus where
  /-- The natural-number modulus. -/
  m : Nat
  /-- Positivity and word-size bounds for the modulus. -/
  [bounds : Bounds m]

/-- A usable word-sized modulus known to be prime. This is the data-carrying
counterpart of the `PrimeModulus` typeclass. -/
structure Prime extends Modulus where
  /-- Project-local primality evidence for the bundled modulus. -/
  prime : Hex.Nat.Prime m

/-- Scan downward through candidates, appending at most `remaining` primes to
`out`. The candidate decreases on every iteration, including rejected
composites, so the scan is fuelled by the finite interval below `candidate`. -/
private def primesBelow.go (remaining candidate : Nat)
    (hbound : candidate < 2 ^ 31) (out : Array Prime) :
    Array Prime :=
  if remaining = 0 || candidate < 2 then
    out
  else if hprime : Hex.Nat.isPrimeTrial candidate = true then
    have prime : Hex.Nat.Prime candidate := Hex.Nat.isPrimeTrial_isPrime hprime
    let bounds : Bounds candidate := { pPos := prime.pos, pLtR := hbound }
    let entry : Prime := { m := candidate, bounds, prime }
    primesBelow.go (remaining - 1) (candidate - 1) (by omega) (out.push entry)
  else
    primesBelow.go remaining (candidate - 1) (by omega) out
termination_by candidate
decreasing_by all_goals simp_all; omega

/-- Return at most the requested number of successive primes below `2^31`, in
descending order starting at `start`. Runtime trial division produces the
primality evidence stored in every result; candidates above the `ZMod64` bound
are skipped by clamping the start of the scan. -/
def primesBelow (start : Nat) : Nat → Array Prime
  | count =>
      primesBelow.go count (min start (2 ^ 31 - 1)) (by omega) #[]

#guard (primesBelow 11 4).map (fun p => p.m) == #[11, 7, 5, 3]

end ZMod64

end Hex
