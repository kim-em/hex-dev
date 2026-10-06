/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.ProofProbe.Support

/-! The negative CFI pair: the Cai-Fürer-Immerman construction over
`K4`, untwisted against twisted, at `n = 40`, under larger limits than
the small examples need. This module is an optional manual correctness build,
outside the CI example target.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 40000000

open Hex.GraphIso Hex.GraphIso.ProofProbe in
theorem Hex.GraphIso.Diagnostics.denseCfi : ¬ Isomorphic (cfi false) (cfi true) := by
  graph_iso (maxSearchNodes := 100000000) (maxCertRecords := 100000000)

/-- info: 'Hex.GraphIso.Diagnostics.denseCfi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.GraphIso.Diagnostics.denseCfi
