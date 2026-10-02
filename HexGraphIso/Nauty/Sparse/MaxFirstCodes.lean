/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFirstEntry
public import HexGraphIso.Nauty.Sparse.FirstCompare
import all HexGraphIso.Nauty.Sparse.MaxFirstEntry
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.PathCodes
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

/-- Adjacent stored code segments concatenate without changing their
literal array indices. -/
theorem StoredCodes.append {store : Array Nat} {base : Nat} {xs ys : List Nat}
    (hx : StoredCodes store base xs) (hy : StoredCodes store (base + xs.length) ys) :
    StoredCodes store base (xs ++ ys) := by
  intro i hi
  by_cases hb : i < xs.length
  · rw [getElem!_append_left hb]
    exact hx i hb
  · have hr : i - xs.length < ys.length := by
      simp only [List.length_append] at hi
      omega
    rw [getElem!_append_right (by omega : xs.length ≤ i) hr]
    have hh := hy (i - xs.length) hr
    simpa only [show base + xs.length + (i - xs.length) = base + i by omega] using hh

namespace Sparse.Max

/-- The actual first descent extends the incoming stored prefix to a
complete first-leaf code sequence. Both comparison machines are initialized
from those literal writes at arbitrary entry depth. -/
theorem FirstEntry.comparison {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel last : Nat} {f : Frame n} {leaf : State n}
    (h : FirstEntry G f)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf) :
    ∃ fs, fs.length = last ∧ f.codes <+: fs ∧
      Comparison G.graph fs fs fs (firstterminal last leaf) := by
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  obtain ⟨xs, U, codes, trace, _, _, htail, _, _, _⟩ :=
    firstPath_history hn path h.frame.positive h.frame.node h.targetSize (by rw [h.firstSize]; omega)
  let fs := f.codes ++ codes
  have hlen : fs.length = last := by
    have ht := trace.length
    have hd := trace.descent.length
    have hl := h.frame.length
    simp only [fs, List.length_append]
    omega
  have hprefix : StoredCodes leaf.firstcode 1 f.codes := by
    intro i hi
    have hb : 1 + i < f.level := by have := h.frame.length; omega
    exact (Prod.mk.inj (firstPath_before path hb)).1.trans (h.stored i hi)
  have hs : StoredCodes leaf.firstcode 1 fs := hprefix.append (by
    have he : 1 + f.codes.length = f.level := by have := h.frame.length; omega
    rw [he]
    exact htail)
  have hvalues : ∀ i, 1 ≤ i → i ≤ fs.length → leaf.firstcode[i]! = fs[i - 1]! := by
    intro i hi hb
    have he := hs (i - 1) (by omega)
    simpa only [show 1 + (i - 1) = i by omega] using he
  have hlt : ∀ code ∈ fs, code < codeSentinel := by
    intro code hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.codes_lt code hc
    · exact trace.codes_lt (refineWith_code_lt _ _ _ _ _ _ _) code hc
  have hleaf := firstPath_ready hn path h.frame.positive h.frame.node
  have hbound : fs.length ≤ n := by
    rw [hlen]
    exact Nat.le_trans hleaf.ok.bc (bcount_le _ _ _)
  have hcanon : leaf.canoncode.size = n + 2 := by rw [firstPath_canoncode path, h.canonSize]
  have hfirst : leaf.firstcode.size = n + 2 := by
    rw [(Prod.mk.inj (firstPath_storeSize path)).1, h.firstSize]
  have hcanonical := firstterminal_codes hcanon hbound hvalues hlt
  have hreference := firstterminal_firstCodeInv hfirst hbound hvalues hlt
  obtain ⟨label, hlabel⟩ := hleaf.parse hn
  have hne : fs ≠ [] := by
    intro he
    have ht := trace.descent.length
    have hl := h.frame.positive
    simp only [he, List.length_nil] at hlen
    omega
  have hm := Comparison.firstterminal (G := G.graph) hcanonical hreference hne hlabel
  rw [hlen] at hm
  exact ⟨fs, hlen, ⟨codes, rfl⟩, hm⟩

/-- The complete first call supplies readable incumbent codes with the
entry's actual prefix. Leaf comparisons and prefix equality are derived
from its executed descent, not supplied as separate proof obligations. -/
theorem FirstEntry.returned {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel last : Nat} {f : Frame n} {leaf : State n}
    (h : FirstEntry G f)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hf : n + 1 ≤ f.level + fuel) :
    ∃ bs fs, ReturnCodes G.graph f.codes bs fs
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2 := by
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  obtain ⟨fs, hlen, hprefix, hm⟩ := h.comparison path
  obtain ⟨bs, hr⟩ := firstPath_returned hn path h.frame.positive h.frame.node h.shape h.targetSize
    (by rw [h.firstSize]; omega) h.blank h.work h.trace hf hlen hm
  have he : fs.take (f.level - 1) = f.codes := by
    have hl : f.level - 1 = f.codes.length := by have := h.frame.length; omega
    rw [hl]
    obtain ⟨tail, he⟩ := hprefix
    rw [← he]
    simp
  rw [he] at hr
  exact ⟨bs, fs, hr⟩

end Sparse.Max
end Hex.GraphIso.Nauty
