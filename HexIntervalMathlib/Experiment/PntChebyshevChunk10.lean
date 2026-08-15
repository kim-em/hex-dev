/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk09

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk10

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 10240 256 104125 = (106851, true) := by decide

private theorem state10496 : checkState 10496 = (106851, true) := by
  simpa using advance Chunk09.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 10496 256 106851 = (109436, true) := by decide

private theorem state10752 : checkState 10752 = (109436, true) := by
  simpa using advance state10496 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 10752 256 109436 = (111880, true) := by decide

private theorem state11008 : checkState 11008 = (111880, true) := by
  simpa using advance state10752 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 11008 256 111880 = (114348, true) := by decide

/-- Authenticated prefix state through coordinate `11264`. -/
theorem state : checkState 11264 = (114348, true) := by
  simpa using advance state11008 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk10

end

