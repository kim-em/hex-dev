/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality
import HexPrimality.Curve25519Replay
import HexPrimality.Curve448Replay

open Hex.Nat

-- Kernel lookup must reject non-represented residues, composites, and primes
-- outside the table; compiled lookup is separately covered by the same API.
example : [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 25, 57467, 99991, 99999, 100000, 100003].map
    isTablePrime =
    [false, false, true, true, false, true, false, true, false, false, true, false,
      true, true, false, false, false] := by
  decide +kernel

/-- info: Try this:
  [apply] exact Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.small 7) (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 7 := by primality?

/--
info: Try this:
  [apply] exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock 57896044618658097711785492504343953926634992332820282019728792003956564819949
        [(2, 0,
            Hex.Nat.PrimeCert.pock3 74058212732561358302231226437062788676166966415465897661863160754340907
              2028478494862525422475607 22304740449229861598212 2028478494862525422475606
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353),
                (2, 0, Hex.Nat.PrimeCert.small 57467),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
                    [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223),
                      (2, 0, Hex.Nat.PrimeCert.small 4153)])])])
      (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime (2 ^ 255 - 19) := by
  primality?

private def expected : PrimeCert :=
  Hex.Nat.PrimeCert.pock 57896044618658097711785492504343953926634992332820282019728792003956564819949
        [(2, 0,
            Hex.Nat.PrimeCert.pock3 74058212732561358302231226437062788676166966415465897661863160754340907
              2028478494862525422475607 22304740449229861598212 2028478494862525422475606
              [(2, 0, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 353),
                (2, 0, Hex.Nat.PrimeCert.small 57467),
                (2, 0,
                  Hex.Nat.PrimeCert.pock3 31757755568855353 4028945 289 4028944
                    [(5, 2, Hex.Nat.PrimeCert.small 2), (2, 0, Hex.Nat.PrimeCert.small 223),
                      (2, 0, Hex.Nat.PrimeCert.small 4153)])])]

private def curveInput : Nat := 2^255 - 19

#guard (match Construction.run curveInput (Hex.Rand.ofSeed curveInput) with
  | .error _ => false
  | .ok s => reprStr s.cert.raw == reprStr expected && s.attempts == 29 &&
      s.rand == Hex.Rand.ofSeed curveInput && checkPrime s.cert.raw)

#guard primesBelow 0 == []
#guard primesBelow 1 == []
#guard primesBelow 2 == []
#guard primesBelow 3 == [2]
#guard primesBelow 4 == [2, 3]
#guard primesBelow 5 == [2, 3]
#guard primesBelow 6 == [2, 3, 5]
#guard [0, 1, 63, 64, 65, 127, 128, 129].all fun count =>
  bitsToListGo (2 ^ 130 - 1) 0 count == (List.range count).map numOfIndex
#guard bitsToListGo (1 <<< 128) 127 3 == [numOfIndex 128]
#guard (List.range 200).all fun n =>
  (primesBelow 200).contains n == isPrimeTrial n
#guard (primesBelow 524288).length == 43390
#guard (primesBelow 524288).getLast? == some 524287
#guard primesBelow 524287 == (primesBelow 524288).dropLast
#guard primesBelow 524289 == primesBelow 524288

private def hardCofactor : Nat :=
  (74058212732561358302231226437062788676166966415465897661863160754340907 - 1) /
    (2 * 3 * 353 * 57467 * 253947789517)

#guard pMinusOneStage1 hardCofactor 2 262144 == .noFactor
#guard pMinusOneStage1 hardCofactor 2 524288 == .factor 31757755568855353
#guard pMinusOneStage1 15 4 2 == .whole
#guard (pMinusOneStage1Counted hardCofactor 2 524288 (Hex.Rand.ofSeed 9)).attempts == 1
#guard (pMinusOneStage1Counted hardCofactor 2 524288 (Hex.Rand.ofSeed 9)).rand ==
  Hex.Rand.ofSeed 9

#guard (match Construction.run 100003 (Hex.Rand.ofSeed 19)
    { constructionBudget with maxDepth := 0 } with
  | .error f => f.stop == .exhausted && f.attempts == 0 && f.rand == Hex.Rand.ofSeed 19
  | _ => false)

private def malformed : FactorSearch := fun _ n r =>
  ⟨⟨[(0, 1), (n + 1, 2 ^ 100)], 0⟩, r, 7⟩

#guard (match Construction.run curveInput (Hex.Rand.ofSeed 19) (factor := malformed) with
  | .error f => f.stop == .exhausted && f.attempts == 7 && f.rand == Hex.Rand.ofSeed 19
  | _ => false)

#guard !checkPrime (.pock curveInput [(2, 0, .small 4)])
#guard !checkPrime (.pock3 31757755568855353 4028945 289 0
  [(5, 2, .small 2), (2, 0, .small 223), (2, 0, .small 4153)])

/--
error: primality?: input has 513 bits; construction limit is 512 bits
-/
#guard_msgs in
example : Hex.Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by primality?

private def rejects (raw : PartialFactors) : Bool :=
  match Construction.run curveInput (Hex.Rand.ofSeed 19)
      (factor := fun _ _ r => ⟨raw, r, 7⟩) with
  | .error f => f.stop == .exhausted && f.attempts == 7 && f.rand == Hex.Rand.ofSeed 19
  | _ => false

#guard rejects ⟨[(2, 2 ^ 100)], 1⟩
#guard rejects ⟨[(2, 1), (2, 1)], 25000⟩
#guard rejects ⟨[(2, 1)], 0⟩
#guard rejects ⟨[(2, 1)], 50000⟩
#guard rejects ⟨[(2, 0)], 100002⟩

set_option pp.all true in
/-- info: Try this:
  [apply] exact Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.small 7) (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 7 := by primality?

namespace SuggestionContext
open Hex.Nat
-- The exact suggested text also elaborates under a namespace with opened APIs.
example : Hex.Nat.Prime 7 := by
  exact Hex.Nat.prime_of_checkPrimeAt (c := Hex.Nat.PrimeCert.small 7) (by decide +kernel)
end SuggestionContext

#guard (Construction.factorSearch constructionBudget.factor 0 (Hex.Rand.ofSeed 3)).raw.residual == 0
#guard (Construction.factorSearch constructionBudget.factor 0 (Hex.Rand.ofSeed 3)).raw.factors.isEmpty

namespace Shadow
private def Hex.Nat.prime_of_checkPrimeAt : Nat := 0
private def Hex.Nat.PrimeCert.small (n : Nat) : Nat := n

/-- info: Try this:
  [apply] exact _root_.Hex.Nat.prime_of_checkPrimeAt (c := _root_.Hex.Nat.PrimeCert.small 7) (by decide +kernel)
-/
#guard_msgs in
example : _root_.Hex.Nat.Prime 7 := by primality?

example : _root_.Hex.Nat.Prime 7 := by
  exact _root_.Hex.Nat.prime_of_checkPrimeAt (c := _root_.Hex.Nat.PrimeCert.small 7) (by decide +kernel)
end Shadow


#guard (match Construction.run curveInput (Hex.Rand.ofSeed curveInput)
    { constructionBudget with maxAttempts := 1 } with
  | .error f => f.stop == .exhausted && f.attempts == 1 &&
      f.rand == Hex.Rand.ofSeed curveInput
  | _ => false)

#guard (match Construction.run curveInput (Hex.Rand.ofSeed curveInput)
    { constructionBudget with maxAttempts := 29 } with
  | .ok s => s.attempts == 29 && reprStr s.cert.raw == reprStr expected
  | _ => false)

#guard (match Construction.run curveInput (Hex.Rand.ofSeed curveInput)
    { constructionBudget with maxAttempts := 28 } with
  | .error f => f.stop == .exhausted && f.attempts == 28
  | _ => false)

#guard (match Construction.run 100003 (Hex.Rand.ofSeed 100003)
    { constructionBudget with maxSubsets := 1 } with
  | .ok s => checkPrime s.cert.raw
  | _ => false)

/--
error: primality?: certificate construction for 57896044618658097711785492504343953926634992332820282019728792003956564819949 exhausted after 1 attempts (seed 57896044618658097711785492504343953926634992332820282019728792003956564819949; maximum 512 bits, recursive depth 32, total attempts 1, factor fuel 1024, p-minus-one bounds [64, 512, 4096, 32768, 262144, 524288] at bases [2, 3], 2 rho restarts with 32768 steps, ECM bounds [] and 0 curves, witness bases [2, 3, 5, 7, 11, 13, 17] then 32 random candidates, at most 12 factors and 4096 subsets, sieve bound at most 64)
-/
#guard_msgs in
example : Hex.Nat.Prime (2 ^ 255 - 19) := by primality? (maxAttempts := 1)


#guard (match Construction.run 2147483647 (Hex.Rand.ofSeed 2147483647)
    { constructionBudget with maxAttempts := 1, witnessBases := [] } with
  | .error f => f.stop == .exhausted && f.attempts == 1 &&
      f.rand == (Hex.Rand.ofSeed 2147483647).next.2
  | _ => false)

-- General cube-root replay and rejection of omitted or false sieve obligations.
example : Hex.Nat.Prime 197 := prime_of_checkPrimeAt
  (c := .pock3Sieve 197 1 6 0 2 [(2, 1, .small 2)]) (by decide +kernel)
#guard !checkPrime (.pock3Sieve 197 1 6 0 1 [(2, 1, .small 2)])
#guard !checkPrime (.pock3Sieve 197 1 6 0 0 [(2, 1, .small 2)])
#guard !checkPrime (.pock3Sieve 205 3 6 0 2 [(32, 1, .small 2)])
#guard checkWitness 205 2 32
#guard !checkDivisors 205 4 1
example : Hex.Nat.Prime 9223372036904058881 := prime_of_checkPrimeAt
  (c := .pock3Sieve 9223372036904058881 47 4194304 0 4 [(3, 19, .small 2)])
  (by decide +kernel)

-- An unusable provider proves the cheap partial-factor route never calls it.
private def noFactors : FactorSearch := fun _ n r => ⟨⟨[], n⟩, r, 1000000⟩
#guard (match Construction.run 9223372036904058881 (Hex.Rand.ofSeed 17)
    (factor := noFactors) with
  | .ok s => checkPrime s.cert.raw && s.attempts < 1000000 && s.rand == Hex.Rand.ofSeed 17
  | _ => false)

/--
info: Try this:
  [apply] exact
    Hex.Nat.prime_of_checkPrimeAt (c :=
      Hex.Nat.PrimeCert.pock3Sieve 9223372036904058881 47 4194304 0 4 [(3, 19, Hex.Nat.PrimeCert.small 2)])
      (by decide +kernel)
-/
#guard_msgs in
example : Hex.Nat.Prime 9223372036904058881 := by primality?

-- Only 2^20 is exposed by table division here. A lower sieve cap must exhaust
-- when the provider declines further factoring, with no consumed factor attempts.
private def decline : FactorSearch := fun _ n r => ⟨⟨[], n⟩, r, 0⟩
example : Hex.Nat.Prime 9223372037728239617 := prime_of_checkPrimeAt
  (c := .pock3Sieve 9223372037728239617 833 4194304 0 4 [(3, 19, .small 2)])
  (by decide +kernel)
#guard (match Construction.run 9223372037728239617 (Hex.Rand.ofSeed 17)
    { constructionBudget with maxSieveBound := 4 } (factor := decline) with
  | .ok s => checkPrime s.cert.raw && s.attempts == 2 && s.rand == Hex.Rand.ofSeed 17
  | _ => false)
#guard (match Construction.run 9223372037728239617 (Hex.Rand.ofSeed 17)
    { constructionBudget with maxSieveBound := 3 } (factor := decline) with
  | .error f => f.stop == .exhausted && f.attempts == 0 && f.rand == Hex.Rand.ofSeed 17
  | _ => false)

-- Arbitrary large literal bounds are rejected before recursive sieve replay.
example : checkPrime (.pock3Sieve 197 1 6 0 1000000000 [(2, 1, .small 2)]) = false := by
  decide +kernel
#guard !checkPrime (.pock3Sieve 197 1 6 0 1000000000 [(2, 1, .small 2)])

-- Both bounds satisfy the size inequality; only the checker cap rejects 65.
example : checkPrime (.pock3Sieve 9223372036904058881 47 4194304 0 64
    [(3, 19, .small 2)]) = true := by decide +kernel
example : checkPrime (.pock3Sieve 9223372036904058881 47 4194304 0 65
    [(3, 19, .small 2)]) = false := by decide +kernel
#guard !checkPrime (.pock3Sieve 9223372036904058881 47 4194304 0 65 [(3, 19, .small 2)])
