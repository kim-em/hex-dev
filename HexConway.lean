/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexConway.Rebuild
public import HexConway.Table
public import HexConway.Certificates
public import HexConway.Api
public import HexConway.Compatibility
public import HexConway.Primitivity
public import HexConway.EntrySource

public section

/-!
Verified imported Conway polynomials, with an exact divisor-closed scope
exported as `Hex.Conway.supportedPairs`. Every entry has irreducibility and
primitivity proofs, including the trivial multiplicative group of GF(2).
Compatibility proofs cover every supported proper-divisor degree pair.
The imported coefficient choice comes from Lübeck; lexicographic minimality
is not proved. Tier 3 on-demand search is unimplemented.

`scripts/conway/generate.py` in hex-dev regenerates all committed data,
certificates, supported-entry APIs and companion specializations offline.
Ordinary builds replay the committed proofs without fetching source data or
searching for certificates. `Rebuild` and `EntrySource` retain the Lean commands
for inspecting coefficient and Tier 1 generation.
-/
