/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGF2Mathlib.Basic
import HexGF2Mathlib.Field

/-!
The `HexGF2Mathlib` library connects the packed `HexGF2` execution path to the
generic proof-facing polynomial and finite-field constructions.

It exposes the packed-polynomial equivalence `Hex.GF2Poly ≃+* Hex.FpPoly 2`
together with the corresponding single-word/arbitrary-degree `GF(2^n)`
correspondence modules.
-/
