/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexMvFactor.Point
public import HexMvHensel.Lift

@[expose] public section

/-!
Construction of validated multivariate-Hensel inputs.

Prime divisibility is rejected before the polynomial witness computation.
`witnessOf?` supplies V6, and the completed value is replayed through
`MvHensel.valid` before it leaves this module.  The starting exponent is a
cheap shifted-coefficient heuristic; successful lifting remains certified by
the exact Hensel checker and never trusts this estimate.
-/

namespace Hex.MvFactor

open Hex
open Hex.MvPoly

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [IsMonomialOrder cmp] [IsMonomialOrder cmp']

/-- Distinguish the cheap V5 rejection from failure to produce V6. -/
inductive InputReject where
  | primeDividesLeading
  | notCoprime
  | invalid (failure : MvHensel.Failure)
  deriving Repr, BEq, DecidableEq

/-- Terminal result of the bounded prime loop. -/
inductive InputSearchReject where
  | invalid (failure : MvHensel.Failure)
  | primesExhausted
  deriving Repr, BEq, DecidableEq

/-- Sum of absolute coefficients, used only as a starting-size heuristic. -/
def coeffOneNorm (p : MvPoly (n + 1) Int cmp) : Nat :=
  p.termsList.foldl (fun total term => total + term.2.natAbs) 0

/-- Twice the shifted one-norm, floored at one. -/
def shiftedEstimate (i : Fin (n + 1)) (point : Fin n → Int)
    (target : MvPoly (n + 1) Int cmp) : Nat :=
  max 1 (2 * coeffOneNorm (MvHensel.shift i point target))

/-- A positive exponent whose power is above twice the heuristic estimate for
every bundled prime (`p ≥ 2`).  Using the base-two logarithm is conservative
for larger primes and avoids a value-sized linear loop. -/
def startingExponent (estimate : Nat) : Nat :=
  (2 * estimate).log2 + 1

/-- Exponents tried after reconstruction failures. -/
def exponentSchedule (initial doublings : Nat) : List Nat :=
  (List.range (doublings + 1)).map fun k => initial * 2 ^ k

/-- V5's allocation-free prime rejection. -/
def primeAvoidsLeading (prime : ZMod64.Prime) (images : List ZPoly) : Bool :=
  images.all fun F => F.leadingCoeff % (prime.m : Int) != 0

/-- Build and independently validate an input at one chosen prime and
exponent. -/
def inputAtPrime (i : Fin (n + 1)) (target : MvPoly (n + 1) Int cmp)
    (probe : Probe n cmp cmp') (prime : ZMod64.Prime) (exponent : Nat) :
    Except InputReject (MvHensel.Input n cmp cmp') :=
  if !primeAvoidsLeading prime probe.images then
    .error .primeDividesLeading
  else
    let setup : MvHensel.Setup n :=
      { main := i, point := probe.point, prime, exponent }
    match MvHensel.witnessOf? setup probe.images with
    | none => .error .notCoprime
    | some witness =>
        let inp : MvHensel.Input n cmp cmp' :=
          { setup
            target
            images := probe.images
            leading := probe.leading
            witness }
        match MvHensel.failure? inp with
        | none => .ok inp
        | some failure => .error (.invalid failure)

/-- Try the supplied primes in order and retain the first fully valid input. -/
def inputFromPrimes (i : Fin (n + 1))
    (target : MvPoly (n + 1) Int cmp) (probe : Probe n cmp cmp')
    (exponent : Nat) : List ZMod64.Prime →
      Except InputSearchReject (MvHensel.Input n cmp cmp')
  | [] => .error .primesExhausted
  | prime :: primes =>
      match inputAtPrime i target probe prime exponent with
      | .ok inp => .ok inp
      | .error .primeDividesLeading =>
          inputFromPrimes i target probe exponent primes
      | .error .notCoprime =>
          inputFromPrimes i target probe exponent primes
      | .error (.invalid failure) => .error (.invalid failure)

/-- Small-prime-first bundled supply used by the EEZ route. -/
def factorPrimes (fuel : Nat) : List ZMod64.Prime :=
  (ZMod64.primesBelow 257 257).toList.reverse.take fuel

/-- Construct the first valid Hensel input for an accepted probe. -/
def inputForProbe? (cfg : Config) (i : Fin (n + 1))
    (target : MvPoly (n + 1) Int cmp) (probe : Probe n cmp cmp') :
    Except InputSearchReject (MvHensel.Input n cmp cmp') :=
  let estimate := shiftedEstimate i probe.point target
  inputFromPrimes i target probe (startingExponent estimate)
    (factorPrimes cfg.primeFuel)

end Hex.MvFactor
