/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk02

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk03

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 3072 256 31260 = (33655, true) := by decide

private theorem state3328 : checkState 3328 = (33655, true) := by
  simpa using advance Chunk02.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 3328 256 33655 = (36512, true) := by decide

private theorem state3584 : checkState 3584 = (36512, true) := by
  simpa using advance state3328 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 3584 256 36512 = (39058, true) := by decide

private theorem state3840 : checkState 3840 = (39058, true) := by
  simpa using advance state3584 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 3840 256 39058 = (41753, true) := by decide

/-- Authenticated prefix state through coordinate `4096`. -/
theorem state : checkState 4096 = (41753, true) := by
  simpa using advance state3840 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk03

end

