/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryLoop
public import HexGraphIso.Nauty.Sparse.BinaryStep

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- The actual singleton-cell iterator admits its complete cell trace.
The cached endpoints of all not-yet-processed cells remain valid. -/
theorem binary_pass (level stamp : Nat) (cells : Array Nat) (s : RefineSt n)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend)
    (hn : cells.toList.Nodup)
    (hc : ∀ a ∈ cells.toList,
      IsCell s.ptn level a (s.cellend[a]! + 1 - a) ∧ a < s.cellend[a]! ∧ s.cellend[a]! < n) :
    Pass level stamp cells.toList s (Id.run do
      let mut s := s
      for first in cells do
        s := Id.run do
          let mut s := s.hash first
          let last := s.cellend[first]! + 1
          let mut lab := s.lab
          s := { s with lab := #[] }
          let mut v2 := first
          let mut hit := #[]
          for j in [first:last] do
            let v := lab[j]!
            if s.vmarks[v]! == stamp then hit := hit.push v
            else
              lab := lab.set! v2 v
              v2 := v2 + 1
          s := s.hash hit.size
          let mut starts := s.cellstart
          s := { s with cellstart := #[] }
          let mut v3 := v2
          for t in [0:hit.size] do
            let j := hit[hit.size - 1 - t]!
            starts := starts.set! j v2
            lab := lab.set! v3 j
            v3 := v3 + 1
          if v2 != v3 && v2 != first then
            if v2 == first + 1 then starts := starts.set! lab[first]! n
            if v3 == v2 + 1 then starts := starts.set! lab[v2]! n
            s := { s with
              numcells := s.numcells + 1, ptn := s.ptn.set! (v2 - 1) level
              cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1) }
            s := s.hash v2
            if v2 - first <= v3 - v2 && !s.active.mem first then s := s.push first
            else s := s.push v2
          return { s with lab, cellstart := starts }
      return s) := by
  let cell (first : Nat) (s : RefineSt n) := Id.run do
    let mut s := s.hash first
    let last := s.cellend[first]! + 1
    let mut lab := s.lab
    s := { s with lab := #[] }
    let mut v2 := first
    let mut hit := #[]
    for j in [first:last] do
      let v := lab[j]!
      if s.vmarks[v]! == stamp then hit := hit.push v
      else
        lab := lab.set! v2 v
        v2 := v2 + 1
    s := s.hash hit.size
    let mut starts := s.cellstart
    s := { s with cellstart := #[] }
    let mut v3 := v2
    for t in [0:hit.size] do
      let j := hit[hit.size - 1 - t]!
      starts := starts.set! j v2
      lab := lab.set! v3 j
      v3 := v3 + 1
    if v2 != v3 && v2 != first then
      if v2 == first + 1 then starts := starts.set! lab[first]! n
      if v3 == v2 + 1 then starts := starts.set! lab[v2]! n
      s := { s with
        numcells := s.numcells + 1, ptn := s.ptn.set! (v2 - 1) level
        cellend := (s.cellend.set! first (v2 - 1)).set! v2 (v3 - 1) }
      s := s.hash v2
      if v2 - first <= v3 - v2 && !s.active.mem first then s := s.push first
      else s := s.push v2
    return { s with lab, cellstart := starts }
  apply pass_loop cell level stamp _ cells s hp hs hi hn hc
  intro first state hp hs hi _hc hf hb
  have hsize : state.lab.size = n := by simpa using hp.length_eq
  exact binary_step level first stamp state (by omega) (by omega) hi.starts_size
    (fun v hv => List.mem_range.mp (hp.mem_iff.mp hv))

end Hex.GraphIso.Nauty.Sparse.Binary
