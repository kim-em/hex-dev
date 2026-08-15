/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk04

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk05

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 5120 256 52240 = (54285, true) := by decide

private theorem state5376 : checkState 5376 = (54285, true) := by
  simpa using advance Chunk04.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 5376 256 54285 = (56990, true) := by decide

private theorem state5632 : checkState 5632 = (56990, true) := by
  simpa using advance state5376 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 5632 256 56990 = (60158, true) := by decide

private theorem state5888 : checkState 5888 = (60158, true) := by
  simpa using advance state5632 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 5888 256 60158 = (62451, true) := by decide

/-- Authenticated prefix state through coordinate `6144`. -/
theorem state : checkState 6144 = (62451, true) := by
  simpa using advance state5888 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk05

end

