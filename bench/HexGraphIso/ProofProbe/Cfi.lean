/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.ProofProbe.Support

/-! The negative CFI pair: the Cai-Fürer-Immerman construction over
`K4`, untwisted against twisted, at `n = 40`, under larger limits than
the other probes need. This module runs on the scheduled profile only,
not in the merge-CI probe build.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 40000000

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : ¬ Isomorphic (cfi false) (cfi true) := by
  graph_iso (maxSearchNodes := 100000000) (maxCertRecords := 100000000)
    (maxKernelSteps := 4000000000)
