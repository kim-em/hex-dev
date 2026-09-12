/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryCell
public import HexGraphIso.Nauty.Sparse.CompactClasses
public import HexGraphIso.Nauty.Sparse.FillRun

public section

namespace Hex.GraphIso.Nauty.Sparse

set_option maxHeartbeats 1000000

/-- One executed singleton-cell body has the control, partition and counter
specified by its number of marked and unmarked input vertices. -/
theorem binary_step (level first stamp : Nat) (s : RefineSt n)
    (hf : first ≤ s.cellend[first]! + 1) (hb : s.cellend[first]! + 1 ≤ s.lab.size)
    (hstarts : s.cellstart.size = n) (hvertices : ∀ v ∈ s.lab.toList, v < n) :
    let last := s.cellend[first]! + 1
    let pred := fun v : Nat => s.vmarks[v]! == stamp
    let r := Id.run do
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
    Binary.Cell level first last pred s r := by
  let last := s.cellend[first]! + 1
  let pred := fun v : Nat => s.vmarks[v]! == stamp
  let seen := (List.range' first (last - first)).map fun q => s.lab[q]!
  let c : Array Nat × Nat × Array Nat := Id.run do
    let mut lab := s.lab
    let mut v2 := first
    let mut hit := #[]
    for j in [first:last] do
      let v := lab[j]!
      if pred v then hit := hit.push v
      else
        lab := lab.set! v2 v
        v2 := v2 + 1
    return (lab, v2, hit)
  have hc : Compact s.lab pred first last seen c.1 c.2.2 c.2.1 :=
    compact_scan s.lab pred first last hf hb
  have hlen : seen.length = last - first := by simp [seen]
  have hextent := hc.extent hlen
  have hhit := congrArg List.length hc.hits
  simp only [Array.length_toList] at hhit
  let restored : Array Nat × Array Nat × Nat := Id.run do
    let mut lab := c.1
    let mut starts := s.cellstart
    let mut v3 := c.2.1
    for t in [0:c.2.2.size] do
      let j := c.2.2[c.2.2.size - 1 - t]!
      starts := starts.set! j c.2.1
      lab := lab.set! v3 j
      v3 := v3 + 1
    return (lab, starts, v3)
  have hrestore : Fill c.1 c.2.2.toList.reverse c.2.1 c.2.2.toList.reverse.length restored.1 ∧
      Index.Writes n s.cellstart restored.2.1 c.2.2.toList.reverse c.2.1 ∧
      restored.2.2 = c.2.1 + c.2.2.size :=
    restore_scan c.1 c.2.2 s.cellstart c.2.1 n
    (by rw [hc.size, hextent]; exact hb) hstarts (by
      intro v hv
      rw [hc.hits] at hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hv).1
      have hq' : q < s.lab.size := by
        simp only [List.mem_range'_1] at hq
        omega
      apply hvertices
      rw [getElem!_pos s.lab q hq']
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hq'))
  have hlast : restored.2.2 = last := hrestore.2.2.trans hextent
  let base := { (s.hash first).hash c.2.2.size with lab := #[], cellstart := #[] }
  have hfinal := binary_control level first c.2.1 restored.2.2 base restored.1 restored.2.1
  have hsource : seen = (s.lab.toList.drop first).take (last - first) := by
    dsimp only [seen]
    rw [List.range'_eq_map_range, List.map_map]
    change segN s.lab first (last - first) = _
    rw [segN_extract s.lab first (last - first) (by have := hc.bounds; omega), Array.toList_extract]
    simp only [List.extract, Nat.add_sub_cancel_left]
  refine ⟨hfinal.control.trans ?_, hfinal.ptn.trans ?_, hfinal.count.trans ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [base, RefineSt.hash, CountTrace.control, CountTrace.Control.hash,
      hlast, hhit, hc.count]
    rfl
  · simp only [base, RefineSt.hash, hlast, hc.count]
    rfl
  · simp only [base, RefineSt.hash, hlast, hc.count]
    rfl
  · have hframe := hfinal.frame
    refine ⟨?_, hframe.ptn_size, ?_, hframe.ends_size, hframe.hits, hframe.marks,
      hframe.vmarks, hframe.stamp, hframe.indexed⟩
    · exact hframe.lab_size.trans (hrestore.1.size.trans hc.size)
    · exact hframe.starts_size.trans (hrestore.2.1.size.trans hstarts.symm)
  · exact hfinal.label.symm ▸ hc.restore hsource hrestore.1
  · refine (congrArg (fun lab => segN lab first
        (first + (seen.filter fun v => !pred v).length - first)) hfinal.label).trans ?_
    simpa only [hc.count, Binary.seen] using hc.kept_segment hrestore.1
  · refine (congrArg (fun lab => segN lab (first + (seen.filter fun v => !pred v).length)
        (last - (first + (seen.filter fun v => !pred v).length))) hfinal.label).trans ?_
    simpa only [hc.count, Binary.seen] using hc.hit_segment hlen hrestore.1

  · intro hp hs hi hcell hn
    exact hfinal.cache (by simpa only [hlast] using hc)
      (by simpa only [hlast] using hsource) hrestore.1 hrestore.2.1 hp hs hi
      (by simpa only [hlast, base, RefineSt.hash, last] using hcell) (by simpa only [hlast] using hn)

end Hex.GraphIso.Nauty.Sparse
