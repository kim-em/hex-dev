/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk01

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk02

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 2048 256 20767 = (23425, true) := by decide

private theorem state2304 : checkState 2304 = (23425, true) := by
  simpa using advance Chunk01.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 2304 256 23425 = (26060, true) := by decide

private theorem state2560 : checkState 2560 = (26060, true) := by
  simpa using advance state2304 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 2560 256 26060 = (28828, true) := by decide

private theorem state2816 : checkState 2816 = (28828, true) := by
  simpa using advance state2560 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 2816 256 28828 = (31260, true) := by decide

/-- Authenticated prefix state through coordinate `3072`. -/
theorem state : checkState 3072 = (31260, true) := by
  simpa using advance state2816 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk02

end
