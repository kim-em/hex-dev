/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIso.ProofProbe.Support

/-! The scheduled negative CFI pair (SPEC release case 4): the
Cai-Fürer-Immerman construction over `K4`, untwisted against twisted,
at `n = 40`, under separately recorded larger limits. Scheduled-only:
this module is not part of the merge-CI probe build.
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 40000000

open Hex.GraphIso Hex.GraphIso.ProofProbe in
example : ¬ Isomorphic (cfi false) (cfi true) := by
  graph_iso (maxNodes := 100000000) (maxCertNodes := 100000000) (maxCheckerSteps := 4000000000)
