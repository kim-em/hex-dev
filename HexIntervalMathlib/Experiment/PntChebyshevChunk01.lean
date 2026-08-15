/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk00

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk01

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 1024 256 10442 = (12948, true) := by decide

private theorem state1280 : checkState 1280 = (12948, true) := by
  simpa using advance Chunk00.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 1280 256 12948 = (15587, true) := by decide

private theorem state1536 : checkState 1536 = (15587, true) := by
  simpa using advance state1280 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 1536 256 15587 = (18340, true) := by decide

private theorem state1792 : checkState 1792 = (18340, true) := by
  simpa using advance state1536 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 1792 256 18340 = (20767, true) := by decide

/-- Authenticated prefix state through coordinate `2048`. -/
theorem state : checkState 2048 = (20767, true) := by
  simpa using advance state1792 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk01

end

