/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPerm

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Count splitting leaves labels outside its original cell unchanged. -/
theorem splitCounts_outside (level first : Nat) (distance : Bool) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]!) (hb : s.cellend[first]! < s.lab.size)
    (q : Nat) (hq : q < first ∨ s.cellend[first]! < q) :
    (splitCounts level first distance s).lab[q]! = s.lab[q]! :=
  (splitCounts_window level first distance s hf hb).outside q (by omega)

end Hex.GraphIso.Nauty.Sparse
