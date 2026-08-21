/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevProbe

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk00

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 0 256 0 = (2574, true) := by decide

private theorem state256 : checkState 256 = (2574, true) := by
  simpa using advance stateZero cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 256 256 2574 = (5254, true) := by decide

private theorem state512 : checkState 512 = (5254, true) := by
  simpa using advance state256 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 512 256 5254 = (7810, true) := by decide

private theorem state768 : checkState 768 = (7810, true) := by
  simpa using advance state512 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 768 256 7810 = (10442, true) := by decide

/-- Authenticated prefix state after the first four bounded chunks. -/
theorem state : checkState 1024 = (10442, true) := by
  simpa using advance state768 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk00

end
