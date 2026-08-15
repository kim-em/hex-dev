/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk03

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk04

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 4096 256 41753 = (44303, true) := by decide

private theorem state4352 : checkState 4352 = (44303, true) := by
  simpa using advance Chunk03.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 4352 256 44303 = (46819, true) := by decide

private theorem state4608 : checkState 4608 = (46819, true) := by
  simpa using advance state4352 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 4608 256 46819 = (49227, true) := by decide

private theorem state4864 : checkState 4864 = (49227, true) := by
  simpa using advance state4608 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 4864 256 49227 = (52240, true) := by decide

/-- Authenticated prefix state through coordinate `5120`. -/
theorem state : checkState 5120 = (52240, true) := by
  simpa using advance state4864 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk04

end

