/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert
public import HexPrimality.Cert3
public import HexPrimality.Elab
public import HexPrimality.MillerRabin
public import HexPrimality.Order
public import HexPrimality.PMinusOne
public import HexPrimality.Search
public import HexPrimality.Sieve
public import HexPrimality.SieveElab
public import HexPrimality.Table

public section

/-!
The `HexPrimality` library provides kernel-checkable primality at scale,
building on hex-arith's `Hex.Nat.Prime` predicate: a committed prime table
with both membership directions, and (per the SPEC) a Miller-Rabin
compositeness filter, Pocklington certificates with a kernel-replayable
checker, a kernel-reducible sieve behind the table, and the `primality`
tactic.
-/
