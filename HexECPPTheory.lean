/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPTheory.Hasse.Degree
public import HexECPPTheory.Hasse.Frobenius
public import HexECPPTheory.Hasse
public import HexECPPTheory.Reduction
public import HexECPPTheory.Order
public import HexECPPTheory.Soundness
public import HexECPPTheory.Elab
public import HexECPPTheory.Compact

/-!
# Proving primality from elliptic curve certificates

`ecpp using c` proves a `Nat.Prime n` goal from a supplied certificate `c`.
The proof interprets its elliptic curve arithmetic over every prime divisor
of `n` and uses Hasse's bound to exclude a small prime divisor. Acceptance by
the executable checker is the only premise of the soundness theorem.

Compact certificates use `ecpp_cert% "rows" using lastPrimeCertificate`.
Import `HexECPPTheory.Native` to find certificates with the built-in search,
or `HexECPPTheory.Pari` to use PARI/GP. Neither search is needed to check a
saved certificate.
-/

@[expose] public section
