/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk05

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk06

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 6144 256 62451 = (65433, true) := by decide

private theorem state6400 : checkState 6400 = (65433, true) := by
  simpa using advance Chunk05.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 6400 256 65433 = (67492, true) := by decide

private theorem state6656 : checkState 6656 = (67492, true) := by
  simpa using advance state6400 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 6656 256 67492 = (70435, true) := by decide

private theorem state6912 : checkState 6912 = (70435, true) := by
  simpa using advance state6656 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 6912 256 70435 = (72865, true) := by decide

/-- Authenticated prefix state through coordinate `7168`. -/
theorem state : checkState 7168 = (72865, true) := by
  simpa using advance state6912 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk06

end
