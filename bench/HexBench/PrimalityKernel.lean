/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimality

/-!
Kernel-replay probes for the `hex-primality` certificate checker.

Each theorem replays `checkPrime` on a committed certificate by kernel
reduction alone (`decide +kernel`), at the same 31/61/123/256/511-bit
rungs the native bench prices with the compiled twin. This module is
build-only: elaborating it measures the kernel side of the
`powModNat`-versus-Montgomery split (the kernel takes the exposed `Nat`
route; the compiled twin dispatches to Montgomery below the word bound),
which is the SPEC's "kernel replay" bench family. Sweep it with a
fresh-module build (delete this module's outputs and rebuild) rather than
in-process timing.

The certificates are the same table-smooth family the native bench uses:
`n - 1 = k · 2^m` with `k` factoring over the committed table, so the
shape is fixed and the exponentiation cost dominates.
-/

namespace HexBench.PrimalityKernel

open Hex.Nat

set_option maxRecDepth 100000

/-- Canonical subjects for the linear structural-preflight replay probe. -/
def longFactors : List (Nat × Nat × PrimeCert) :=
  (List.range 1024).map fun i => (0, 0, .small (i + 2))

theorem replayLongSubjects : subjectsOk longFactors = true := by
  decide +kernel

theorem rejectLateDuplicate :
    subjectsOk (longFactors ++ [(0, 0, .small 1025)]) = false := by
  decide +kernel

def cert31 : PrimeCert :=
  .pock 2147483647
    [(1745337962, 0, .small 2), (1371693800, 1, .small 3),
     (1615909500, 0, .small 7), (447824900, 0, .small 11),
     (505209180, 0, .small 31), (1783259301, 0, .small 151),
     (904659249, 0, .small 331)]

def cert61 : PrimeCert :=
  .pock 1945555039024054273
    [(891154892214722695, 55, .small 2), (110189291828549774, 2, .small 3)]

def cert123 : PrimeCert :=
  .pock 9304595970494411110326649421962412033
    [(14072917602864530050, 119, .small 2),
     (13757245211066428521, 0, .small 7)]

def cert256 : PrimeCert :=
  .pock 93628759656736142393278101159368737990730026663232799828780155818898507169793
    [(8195237237126968763, 247, .small 2),
     (13757245211066428521, 1, .small 3),
     (10451216379200822467, 0, .small 23)]

def cert511 : PrimeCert :=
  .pock 6651529715244960279866801463953681477304216637559507652230048059971343874294298695522804827606237247330601742147202064290729465301239118684363568061612033
    [(13757245211066428521, 503, .small 2),
     (10451216379200822467, 0, .small 127)]

theorem replay31 : checkPrime cert31 = true := by decide +kernel

theorem replay61 : checkPrime cert61 = true := by decide +kernel

theorem replay123 : checkPrime cert123 = true := by decide +kernel

theorem replay256 : checkPrime cert256 = true := by decide +kernel

theorem replay511 : checkPrime cert511 = true := by decide +kernel

/-- The cube-root checker arm also replays through the kernel-facing closure. -/
theorem replayPock3 :
    checkPrime
      (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true := by
  decide +kernel

end HexBench.PrimalityKernel
