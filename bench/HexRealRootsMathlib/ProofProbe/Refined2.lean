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

/-! Width-`2⁻²⁰` replay on the Wilkinson degree-2 product. -/

set_option maxHeartbeats 1000000 in
noncomputable def refined2 :
    IsolatedRealRoots ((X - 1) * (X - 2) : Polynomial ℤ) 2 :=
  isolate_roots (width := 2 ^ (-20 : ℤ)) ((X - 1) * (X - 2) : Polynomial ℤ)

#print axioms refined2

end HexRealRootsMathlib.ProofProbe
