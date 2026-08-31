/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexIntFactor
public import HexIntFactor

/-! Downstream conformance for the HexIntFactor primality-search adapter. -/

open Hex Hex.Nat

private def squarePrime : Nat := 1208925821721293454442757

private def squareFactor : Nat := 549755814367

private def squareSeed : Rand := Rand.ofSeed squarePrime

private def squareFuel : Nat := min (defaultPrimeFuel squarePrime) 512

private def tacticBudget : PrimeCertBudget := ⟨2, 1 <<< 15⟩

private def squareAllocation (factorFuel : Nat) : FactorSearchBudget :=
  ⟨tacticBudget, squareFuel - 1, factorFuel⟩

private def coreFailure : PrimeCertFailure :=
  match Internal.primeCertCountedWith? tacticBudget squarePrime squareSeed
      squareFuel with
  | .error failure => failure
  | .ok _ => ⟨.composite, 0, squareSeed⟩

-- The ordinary elaborator allocation exhausts on this prime. Its advanced
-- state is the exact starting point for deterministic extension dispatch.
#guard coreFailure.stop == .exhausted
#guard coreFailure.attempts == 8
#guard coreFailure.rand == (squareSeed.words 18).2

-- HexIntFactor recognizes `(squarePrime - 1) = 4 * squareFactor^2`. The
-- adapter exposes the checked aggregate as untrusted factor-search data and
-- retains the producer's exact accounting and state.
private def squareSearch : FactorSearchResult :=
  intFactorSearch (squareAllocation (2 * squarePrime.log2 + 8))
    (squarePrime - 1) coreFailure.rand

#guard squareSearch.raw.factors == [(2, 2), (squareFactor, 2)]
#guard squareSearch.raw.residual == 1
#guard squareSearch.attempts == 20
#guard squareSearch.rand == (squareSeed.words 38).2

-- Zero fuel retains the checker-accepted structural progress without running
-- a randomized continuation.
private def squareSearchEmpty : FactorSearchResult :=
  intFactorSearch (squareAllocation 0) (squarePrime - 1) squareSeed

#guard squareSearchEmpty.raw.factors == [(2, 2)]
#guard squareSearchEmpty.raw.residual == squareFactor ^ 2
#guard squareSearchEmpty.attempts == 0
#guard squareSearchEmpty.rand == squareSeed

-- The stronger producer finishes certificate construction from the resumed
-- state. Its own subtotal and final state exclude the earlier core subtotal;
-- the elaborator combines the two only for exhaustion diagnostics.
#guard (match Internal.primeCertCountedUsing? intFactorSearch tacticBudget
    squarePrime coreFailure.rand squareFuel with
  | .ok success =>
      success.cert.raw.subject == squarePrime &&
        checkPrime success.cert.raw && success.attempts == 41 &&
          success.rand == (squareSeed.words 61).2
  | .error _ => false)

-- Import-time registration transparently gives the ordinary syntax the same
-- stronger route. The emitted proof still replays only `checkPrime`.
example : Hex.Nat.Prime 1208925821721293454442757 :=
  primality 1208925821721293454442757

-- Import-time registration does not disturb the core composite verdict or
-- its concrete Miller--Rabin diagnostic.
/-- error: primality: 561 is not prime (Miller-Rabin witness 2) -/
#guard_msgs in
example : Hex.Nat.Prime 561 := primality 561
