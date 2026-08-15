/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Experiment.PntChebyshevChunk06

@[expose] public section

namespace Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk07

open Hex.IntervalMathlib.Experiment.PntChebyshevProbe

set_option maxRecDepth 100000 in
private theorem cert0 : checkChunk 7168 256 72865 = (75115, true) := by decide

private theorem state7424 : checkState 7424 = (75115, true) := by
  simpa using advance Chunk06.state cert0

set_option maxRecDepth 100000 in
private theorem cert1 : checkChunk 7424 256 75115 = (78026, true) := by decide

private theorem state7680 : checkState 7680 = (78026, true) := by
  simpa using advance state7424 cert1

set_option maxRecDepth 100000 in
private theorem cert2 : checkChunk 7680 256 78026 = (80711, true) := by decide

private theorem state7936 : checkState 7936 = (80711, true) := by
  simpa using advance state7680 cert2

set_option maxRecDepth 100000 in
private theorem cert3 : checkChunk 7936 256 80711 = (83085, true) := by decide

/-- Authenticated prefix state through coordinate `8192`. -/
theorem state : checkState 8192 = (83085, true) := by
  simpa using advance state7936 cert3

end Hex.IntervalMathlib.Experiment.PntChebyshevProbe.Chunk07

end

