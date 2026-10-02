/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountPass

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

/-- A pending count cell retains its original endpoints and exact semantic
counts until its turn in the native touched-cell loop. -/
structure Ready (level : Nat) (key : Nat → Nat) (first last : Nat) (s : RefineSt n) : Prop where
  cell : IsCell s.ptn level first (last + 1 - first)
  le : first ≤ last
  bound : last < n
  keys : ∀ q, first ≤ q → q ≤ last → s.hits[s.lab[q]!]! < n + 2
  values : ∀ v ∈ segN s.lab first (last + 1 - first), s.hits[v]! = key v

/-- Valid endpoint caches agree with the original pending cell. -/
theorem Ready.endpoint {s : RefineSt n} (h : Ready level key first last s)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend) : s.cellend[first]! = last := by
  have := hi.ends_eq first (last + 1 - first) h.cell (by have := h.le; have := h.bound; omega)
    (by have := h.le; have := h.bound; omega)
  have := h.le
  omega

/-- Processing a different cell leaves pending cell keys and their exact
semantic values intact, as well as its partition boundaries. -/
theorem Ready.keep {s : RefineSt n} (h : Ready level key first last s)
    (other : Ready level key a b s) (hne : a ≠ first) (distance : Bool)
    (hp : s.lab.toList.Perm (List.range n)) (hs : s.ptn.size = n)
    (hi : Index.Valid n s.lab s.ptn level s.cellstart s.cellend) :
    Ready level key a b (splitCounts level first distance s) := by
  have he := h.endpoint hi
  have hl : s.lab.size = n := by simpa using hp.length_eq
  have hh := h.le
  have hb := h.bound
  have ha := other.le
  have hc := other.bound
  have hd : b < first ∨ last < a := by
    rcases isCell_disjoint_or_eq h.cell other.cell with ho | ho | ho
    · left; omega
    · right; omega
    · exact False.elim (hne ho.1.symm)
  have hkey : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2 := by
    simpa only [he] using h.keys
  have hout (q : Nat) (hq : a ≤ q) (hu : q ≤ b) :
      (splitCounts level first distance s).lab[q]! = s.lab[q]! :=
    splitCounts_outside level first distance s (by omega) (by omega) q (by omega)
  refine ⟨(splitCounts_partition level first distance s hl hs (by omega) (by omega)
    hkey).preserve other.cell (by omega), ha, hc, ?_, ?_⟩
  · intro q hq hu
    rw [(splitCounts_frame level first distance s).hits, hout q hq hu]
    exact other.keys q hq hu
  · intro v hv
    obtain ⟨i, hi, hv⟩ := mem_segN_iff.mp hv
    rw [hout (a + i) (by omega) (by omega)] at hv
    rw [(splitCounts_frame level first distance s).hits]
    exact other.values v (mem_segN_iff.mpr ⟨i, hi, hv⟩)

end Hex.GraphIso.Nauty.Sparse.CountTrace
