/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality.Inputs

/-!
Kernel-replay probes for the `hex-primality` certificate checker.

The certificate theorems replay `checkPrime` by kernel reduction alone
(`decide +kernel`) at the same 31/61/123/256/511-bit rungs the native bench
prices with the compiled twin. Two further theorems replay the structural
preflight over 1024 entries, accepting canonical subjects and rejecting a
duplicate in the final slot. This module is build-only: elaborating it
measures the kernel side of the
`powModNat`-versus-Montgomery split (the kernel takes the exposed `Nat`
route; the compiled twin dispatches to Montgomery below the word bound),
which is the SPEC's "kernel replay" bench family. Sweep it with a
fresh-module build (delete this module's outputs and rebuild) rather than
in-process timing.

The certificates are the same fixed family the native bench uses. The lower
rungs are table-smooth; the 512-bit policy rung contains the recursive
certificate for the above-table factor `100297` discovered by bounded rho.
-/

namespace HexBench.PrimalityKernel

open Hex.Nat
open Hex.PrimalityBench

set_option maxRecDepth 100000

/-- Canonical subjects for the linear structural-preflight replay probe. -/
def longFactors : List (Nat × Nat × PrimeCert) :=
  (List.range 1024).map fun i => (0, 0, .small (i + 2))

theorem replayLongSubjects : subjectsOk longFactors = true := by
  decide +kernel

theorem rejectLateDuplicate :
    subjectsOk (longFactors ++ [(0, 0, .small 1025)]) = false := by
  decide +kernel

theorem replay31 : checkPrime primalityCert31 = true := by decide +kernel

theorem replay61 : checkPrime primalityCert61 = true := by decide +kernel

theorem replay123 : checkPrime primalityCert123 = true := by decide +kernel

theorem replay256 : checkPrime primalityCert256 = true := by decide +kernel

theorem replay511 : checkPrime primalityCert511 = true := by decide +kernel

theorem replay512 : checkPrime primalityCert512 = true := by decide +kernel

/-- The cube-root checker arm also replays through the kernel-facing closure. -/
theorem replayPock3 :
    checkPrime
      (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true := by
  decide +kernel

end HexBench.PrimalityKernel
