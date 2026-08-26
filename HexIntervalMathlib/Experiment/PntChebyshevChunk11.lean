/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk10

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk11

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 11264 256 114348 = (116961, true) := by decide

private theorem state11520 : checkState 11520 = (116961, true) := by
  simpa using advance Chunk10.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 11520 203 116961 = (118671, true) := by decide

/-- Authenticated prefix state through coordinate `11723`. -/
theorem state : checkState 11723 = (118671, true) := by
  simpa using advance state11520 cert1

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk11

end
