/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Data
public import HexECPP.Affine
public import HexECPP.Replay
public import HexECPP.Cert
public import HexECPP.Import
public import HexECPP.CM
public import HexECPP.Search

public section

/-!
# Elliptic curve primality proving

ECPP proves an integer prime by finding an elliptic curve point of sufficiently
large prime order. A certificate records the curve, point, modular inverses and
a certificate for that smaller prime. This library supplies the data, an
executable checker, conversion of PARI certificate text and a built-in search.

Import `HexECPPMathlib` for the theorem that checker acceptance implies
Mathlib's `Nat.Prime`, or `HexECPPMathlib.Native` to search from a primality
goal. The computational library here imports no Mathlib modules.
-/
