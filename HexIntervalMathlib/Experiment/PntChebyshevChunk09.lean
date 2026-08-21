/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk08

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk09

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 9216 256 93590 = (96520, true) := by decide

private theorem state9472 : checkState 9472 = (96520, true) := by
  simpa using advance Chunk08.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 9472 256 96520 = (98938, true) := by decide

private theorem state9728 : checkState 9728 = (98938, true) := by
  simpa using advance state9472 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 9728 256 98938 = (101728, true) := by decide

private theorem state9984 : checkState 9984 = (101728, true) := by
  simpa using advance state9728 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 9984 256 101728 = (104125, true) := by decide

/-- Authenticated prefix state through coordinate `10240`. -/
theorem state : checkState 10240 = (104125, true) := by
  simpa using advance state9984 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk09

end
