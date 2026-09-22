/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexIntFactor
public import HexIntFactor

/-!
Downstream conformance for the HexIntFactor primality-search adapter.

Oracle: none; this module checks the adapter against the independently
checker-accepted HexIntFactor aggregate and the HexPrimality consumer boundary.
Mode: `always`
Covered operations:
- `intFactorSearch`, `Internal.primeCertCountedUsing?`, and the registered
  `HexIntFactor.PrimalityTactic.extension`
Covered properties:
- complete and partial aggregates preserve factors, residual, attempt totals,
  and random state across the untrusted adapter boundary
- extension dispatch resumes from the core route's terminal state and emitted
  proof terms replay `checkPrime`
Covered edge cases:
- zero factor fuel, core exhaustion, an 81-bit perfect-power witness, and a
  composite input with a stable Miller--Rabin diagnostic
-/

open Hex Hex.Nat

private def squarePrime : Nat := 1208925821721293454442757

private def squareFactor : Nat := 549755814367

private def squareSeed : Rand := Rand.ofSeed squarePrime

private def squareFuel : Nat := min (defaultPrimeFuel squarePrime) 512

private def tacticBudget : PrimeCertBudget := ⟨2, 1 <<< 15⟩

private def squareAllocation (factorFuel : Nat) : FactorSearchBudget :=
  { primeBudget := tacticBudget, primeFuel := squareFuel - 1, factorFuel := factorFuel }

private def coreFailure : PrimeCertFailure :=
  match Internal.primeCertCountedWith? tacticBudget squarePrime squareSeed
      squareFuel with
  | .error failure => failure
  | .ok _ => ⟨.composite, 0, squareSeed, []⟩

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

-- The two registrations expose different schedules and separate ABI versions.
run_cmd Lean.Elab.Command.liftTermElabM do
  let some ext ← Hex.PrimalityTactic.constructionExtension?
      `HexIntFactor.PrimalityTactic.constructionExtension
    | throwError "missing construction registration"
  unless ext.version == 1 && ext.factorName == ``Hex.Nat.ecmConstructionFactor do
    throwError "incorrect construction registration"
  unless (← Hex.PrimalityTactic.searchExtensions).any
      (fun ext => ext.version == 3 && ext.factorName == ``Hex.Nat.intFactorSearch) do
    throwError "ordinary search registration changed"

-- The ordinary adapter must decline a total-limit construction allocation.
private def boundedAdapter : FactorSearchResult :=
  intFactorSearch { constructionBudget.factor with attemptLimit := some 1024 }
    1000002 (Rand.ofSeed 19)

#guard boundedAdapter.raw.factors.isEmpty && boundedAdapter.raw.residual == 1000002 &&
  boundedAdapter.attempts == 0 && boundedAdapter.rand == Rand.ofSeed 19 && boundedAdapter.events.isEmpty

-- Standard HexIntFactor import: even with ECM registered, an explicit adapter
-- that declines total limits must exhaust instead of activating automatic ECM.
/--
error: primality?: certificate construction for 1000003 exhausted after 0 attempts (seed 1000003; maximum 521 bits, recursive depth 32, total attempts 1024, factor fuel 1024, explicit factor provider Hex.Nat.intFactorSearch (its per-attempt bounds apply), witness bases [2, 3, 5, 7, 11, 13, 17] then 32 random candidates, at most 32 factors and 4096 subsets, sieve bound at most 64); unresolved obligation 1000003
-/
#guard_msgs in
example : Hex.Nat.Prime 1000003 := by
  primality? (factor := Hex.Nat.intFactorSearch)

-- Registered providers impose no search on successes of the first route.
run_cmd Lean.Elab.Command.liftTermElabM do
  for (n, attempts) in [(2^521 - 1, 170), (2^255 - 19, 29)] do
    let .ok first := Construction.run n (Rand.ofSeed n)
      | throwError "core regression"
    let (result, allocations) ← Hex.PrimalityTactic.construct n constructionBudget
    let .ok result := result | throwError "automatic regression"
    unless allocations.isEmpty && result.attempts == attempts &&
        result.attempts == first.attempts && result.rand == first.rand &&
        result.events == first.events && reprStr result.cert.raw == reprStr first.cert.raw do
      throwError "first-route success changed"
