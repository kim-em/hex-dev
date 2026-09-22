/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Construction

-- A handle cannot be forged or edited through public record syntax.
example (t : Hex.Nat.Ecm.Tables) : Hex.Nat.Ecm.Tables := by
  fail_if_success exact { t with powers := some [] }
  exact t

namespace Hex.Nat.Ecm.Test

-- Test-only trial division, independent of the production runtime sieve.
private def primes (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter fun n =>
    n ≥ 2 && (List.range (n.sqrt + 1)).all (fun d => d < 2 || n % d != 0)

private def power (p bound : Nat) : Nat := Id.run do
  let mut k := p
  for _ in [:bound] do
    if k * p > bound then break
    k := k * p
  return k

set_option maxHeartbeats 4000000 in
#eval show IO Unit from do
  for (b₁, b₂) in [(0, 0), (0, 2), (1, 1), (1, 2), (16, 16), (16, 17),
      (64, 63), (64, 66), (64, 67), (64, 199), (64, 211), (64, 419),
      (64, 421), (64, 431), (64, 1021), (64, 8191)] do
    let some t := prepare b₁ b₂ | throw (IO.userError "valid bounds rejected")
    unless t.powers.isNone && t.primes.isNone do throw (IO.userError "eager preparation")
    let (zero, t) := Internal.searchPrepared (2^127-1) 6 0 t
    unless zero == (.noFactor, 0) && t.powers.isNone && t.primes.isNone do
      throw (IO.userError "zero allowance prepared tables")
    let (_, t) := Internal.searchPrepared (2^127-1) 6 1 t
    unless t.powers == some ((primes b₁).map (power · b₁)) && t.primes.isNone do
      throw (IO.userError "stage-1 enumeration or eager stage 2")
    let (result, t) := Internal.searchPrepared (2^127-1) 6 2 t
    unless result == search (2^127-1) 6 b₁ b₂ 2 do throw (IO.userError "search mismatch")
    let expected := if b₁ < b₂ then some ((primes b₂).filter (b₁ < ·)) else none
    unless t.primes == expected do throw (IO.userError "stage-2 enumeration")
    for n in [15, 1009, 1022117, 1000036000099] do
      for sigma in [6:10] do
        for allowance in [0, 1, 2, 3] do
          unless (Internal.searchPrepared n sigma allowance t).1 == search n sigma b₁ b₂ allowance do
            throw (IO.userError "shared curve/residual mismatch")
  unless (prepare 524289 1024).isNone && (prepare 64 4194305).isNone &&
      (prepare 524288 4194304).isSome do throw (IO.userError "bound validation")
  let some t := prepare 64 1024 | throw (IO.userError "bounds")
  for (n, sigma) in [(0, 6), (3, 6), (15, 5), (15, 6)] do
    let (_, t) := Internal.searchPrepared n sigma 2 t
    unless t.powers.isNone && t.primes.isNone do throw (IO.userError "setup allocated schedules")
  unless Internal.flush 1081 0 #[0, 23] == (.factor 23, [1081, 23]) do
    throw (IO.userError "whole-leaf recovery")
  IO.println "ECM schedule conformance passed"

end Hex.Nat.Ecm.Test
