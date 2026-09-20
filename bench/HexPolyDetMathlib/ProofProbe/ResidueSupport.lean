/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Field.ZMod
import HexPrimalityMathlib

/-- Domain evidence supplied equally to the determinant probes and baselines. -/
instance : Fact (Nat.Prime 2147483647) := ⟨by primality⟩
