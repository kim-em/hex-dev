/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.MaximalCoefficients

/-- Require completion of every source inventory and kernel-equivalence check
in a fresh ordinary module, including after an interrupted producer module. -/
example : True := Hex.RCF.RealCoefficients.MaximalCoefficientsTests.complete
