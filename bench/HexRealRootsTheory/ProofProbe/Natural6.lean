/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsTheory.IsolateRootsElab

public section

open Hex Polynomial

namespace HexRealRootsTheory.ProofProbe

/-! Natural-width `isolate_roots` replay on the Wilkinson degree-6 product. -/

set_option maxHeartbeats 1000000 in
noncomputable def natural6 :
    IsolatedRealRoots
      ((X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) * (X - 6) :
        Polynomial ℤ) 6 :=
  isolate_roots
    ((X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) * (X - 6) :
      Polynomial ℤ)

/-- info: 'HexRealRootsTheory.ProofProbe.natural6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natural6

end HexRealRootsTheory.ProofProbe
