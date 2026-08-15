/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk07

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk08

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 8192 256 83085 = (85753, true) := by decide

private theorem state8448 : checkState 8448 = (85753, true) := by
  simpa using advance Chunk07.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 8448 256 85753 = (88237, true) := by decide

private theorem state8704 : checkState 8704 = (88237, true) := by
  simpa using advance state8448 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 8704 256 88237 = (90905, true) := by decide

private theorem state8960 : checkState 8960 = (90905, true) := by
  simpa using advance state8704 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 8960 256 90905 = (93590, true) := by decide

/-- Authenticated prefix state through coordinate `9216`. -/
theorem state : checkState 9216 = (93590, true) := by
  simpa using advance state8960 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk08

end

