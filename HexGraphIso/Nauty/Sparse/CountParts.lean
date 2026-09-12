/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The named count-sort blocks are literally the executed splitter. -/
theorem splitCounts_parts (level first : Nat) (distance : Bool) (s : RefineSt n) :
    splitCounts level first distance s =
      let lab := s.lab
      let hits := s.hits
      let last := s.cellend[first]! + 1
      let r := s.hash first
      let v2 := CountSort.firstRun lab hits first last
      if v2 == last then r else
        let m := CountSort.minima lab hits (n + 2) first last v2
        CountSort.finish level first last distance { r with lab := m.2.2.2.2 }
          m.1 m.2.1 m.2.2.1 m.2.2.2.1 := by
  rfl

end Hex.GraphIso.Nauty.Sparse
