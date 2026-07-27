/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus

public section

/-!
# Release 4: the lattice-backed factorization seam

Swinnerton--Dyer SD₆ has degree 64 and splits into 32 modular factors at the
selected prime. Classical subset recombination therefore declines at its
bounded complete level; the production dispatcher answers through the CLD/LLL
lattice tier. The single check below pins the dispatch tier, exact product, and
singleton factor shape without invoking the trial backstop.
-/

namespace Examples.Release4

open Hex

/-- Swinnerton--Dyer SD₆, the first committed production lattice rung. -/
def input : ZPoly := DensePoly.ofCoeffs
  #[198828783273803025550632280753863681, 0,
    -8316202966928528723117528333532208416, 0,
    100392008259975194458539996111340080624, 0,
    -511762449216265420619809586571618679392, 0,
    1258829468814790188483900997578812102776, 0,
    -1771080720430629161685158978892152599456, 0,
    1585722240968892813653220405983168716752, 0,
    -968316307427310602872375357706532108000, 0,
    423140580409718469187953106123559340828, 0,
    -137048942135190916858196960829292680864, 0,
    33785494292069713784801456649105169648, 0,
    -6471399892949448329687739464771529952, 0,
    978878175154164215599705915851796296, 0,
    -118444912349891951852181962142375200, 0,
    11582497564629879101390954172990800, 0,
    -922739669127277027441017551584608, 0,
    60261059130667890854325275719238, 0,
    -3240853899326109989616514647392, 0,
    143976257181996292530653998416, 0,
    -5292590468585153795497272608, 0,
    161038437520893531719546696, 0,
    -4051269676739248306877664, 0,
    84041236543621002233072, 0,
    -1431186296399427673760, 0,
    19875965471079809820, 0,
    -223010452468129504, 0,
    1995413247403984, 0,
    -13981172308896, 0,
    74737287288, 0,
    -293134944, 0,
    792048, 0,
    -1312, 0, 1]

/-- Force the full result and reject a classical or trial answer. -/
def check : Bool :=
  let result := factorTraced input
  result.2.tier == "lattice" && result.2.declined &&
    DensePoly.beqCoeffs (Factorization.product result.1) input &&
    result.1.factors.size == 1

#guard check

end Examples.Release4
