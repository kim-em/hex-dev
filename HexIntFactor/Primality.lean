/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPrimality.Elab
public meta import HexIntFactor.Factor
public import HexPrimality.Elab
public import HexIntFactor.Factor

public section

/-!
The downstream partial-factor adapter for HexPrimality certificate search.

The adapter projects HexIntFactor's checker-accepted complete or partial
aggregate into HexPrimality's deliberately untrusted `FactorSearchResult`.
Importing this module also registers the adapter with the `primality`
elaborator through its versioned, well-known declaration boundary. The core
route runs first; this stronger route is tried only after core exhaustion.
-/

namespace Hex

namespace Nat

private def factorPairs (entries : List PrimePower) : List (Nat × Nat) :=
  entries.map fun entry => (entry.prime, entry.exponent)

/-- HexIntFactor's bounded search projected to HexPrimality's untrusted
partial-factor callback. Complete results use residual one; incomplete results
retain the last checker-accepted snapshot. A rejected internal candidate
degrades to the checker's trivial saved snapshot; only zero lacks a snapshot
and returns the honest empty candidate with residual zero. -/
def intFactorSearch : FactorSearch := fun allocation n r =>
  match Internal.factorCountedWith? allocation.primeBudget
      allocation.primeFuel n r allocation.factorFuel with
  | .ok success =>
      ⟨⟨factorPairs success.factorization.raw.factors, 1⟩,
        success.rand, success.attempts⟩
  | .error failure =>
      match failure.snapshot with
      | some saved =>
          ⟨⟨factorPairs saved.raw.factors, saved.raw.residual⟩,
            failure.rand, failure.attempts⟩
      | none => ⟨⟨[], n⟩, failure.rand, failure.attempts⟩

end Nat

end Hex

namespace HexIntFactor.PrimalityTactic

/-- The HexIntFactor search extension, discovered by name from
`Hex.PrimalityTactic.searchExtensionNames`. -/
public meta def extension : Hex.PrimalityTactic.SearchExtension where
  version := Hex.PrimalityTactic.searchExtensionVersion
  factorName := ``Hex.Nat.intFactorSearch

end HexIntFactor.PrimalityTactic
