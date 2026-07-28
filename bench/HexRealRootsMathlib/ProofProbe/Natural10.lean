/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.IsolateRootsElab

public section

open Hex Polynomial

namespace HexRealRootsMathlib.ProofProbe

/-! Natural-width `isolate_roots` replay on the Wilkinson degree-10 product. -/

set_option maxHeartbeats 1000000 in
noncomputable def natural10 :
    IsolatedRealRoots
      ((X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) * (X - 6) *
        (X - 7) * (X - 8) * (X - 9) * (X - 10) : Polynomial ℤ) 10 :=
  isolate_roots
    ((X - 1) * (X - 2) * (X - 3) * (X - 4) * (X - 5) * (X - 6) *
      (X - 7) * (X - 8) * (X - 9) * (X - 10) : Polynomial ℤ)

#print axioms natural10

end HexRealRootsMathlib.ProofProbe
