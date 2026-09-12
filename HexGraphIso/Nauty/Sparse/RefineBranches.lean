/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineSelect

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt.Equiv

/-- The native singleton branch transports at valid working states. -/
theorem singleton (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    {s t : RefineSt n} (h : Equiv (renamingOf p) level s t)
    (hs : Valid level s) (ht : Valid level t) (split : Nat)
    (hb : split < n) (hc : IsCell s.ptn level split 1) :
    Equiv (renamingOf p) level (splitSingleton (.ofGraph G) level split s)
      (splitSingleton (.ofGraph H) level split t) := by
  have hh := splitSingleton_equiv G H p hiso level split s t hs.lab ht.lab hs.size h.ptn hs.closed hb hc
    hs.index ht.index h.cells ⟨hs.scratch.marks_size, hs.scratch.marks_le⟩
    ⟨hs.scratch.vmarks_size, hs.scratch.vmarks_le⟩
    ⟨ht.scratch.marks_size, ht.scratch.marks_le⟩ ⟨ht.scratch.vmarks_size, ht.scratch.vmarks_le⟩
    h.control h.count
  exact ⟨hh.1.symm, hh.2.1, hh.2.2.1, hh.2.2.2⟩

/-- The native nontrivial branch transports at valid working states. -/
theorem nontrivial (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    {s t : RefineSt n} (h : Equiv (renamingOf p) level s t)
    (hs : Valid level s) (ht : Valid level t) (split len : Nat)
    (hc : IsCell s.ptn level split len) (hb : split + len ≤ n) :
    Equiv (renamingOf p) level (splitNontrivial (.ofGraph G) level split s)
      (splitNontrivial (.ofGraph H) level split t) := by
  have hh := splitNontrivial_equiv G H p hiso level split len s t hs.lab ht.lab hs.size h.ptn hs.closed hc hb
    hs.index ht.index h.cells ⟨hs.scratch.marks_size, hs.scratch.marks_le⟩ hs.scratch.hits_size
    ⟨ht.scratch.marks_size, ht.scratch.marks_le⟩ ht.scratch.hits_size h.control h.count
  exact ⟨hh.1.symm, hh.2.1, hh.2.2.1, hh.2.2.2⟩

/-- The actual selected queue entry, swap/pop removal, hash and branch
dispatch transport together. -/
theorem selected (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    {s t : RefineSt n} (h : Equiv (renamingOf p) level s t)
    (hs : Valid level s) (ht : Valid level t) (pos : Nat) (hp : pos < s.queue.size) :
    Equiv (renamingOf p) level (RefineSt.selected (.ofGraph G) level pos s)
      (RefineSt.selected (.ofGraph H) level pos t) := by
  have hp' : pos < t.queue.size := h.queue ▸ hp
  have hc := hs.queue_cell hp
  let a := ({ s with
    active := s.active.erase s.queue[pos]!
    queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop }).hash s.queue[pos]!
  let b := ({ t with
    active := t.active.erase t.queue[pos]!
    queue := (t.queue.set! pos t.queue[t.queue.size - 1]!).pop }).hash t.queue[pos]!
  have ha : Valid level a := (hs.remove hp).hash s.queue[pos]!
  have hb : Valid level b := (ht.remove hp').hash t.queue[pos]!
  have he : Equiv (renamingOf p) level a b := by
    simpa only [a, b, h.queue] using (h.remove pos).hash s.queue[pos]!
  have htest : (t.ptn[t.queue[pos]!]! ≤ level) ↔ (s.ptn[s.queue[pos]!]! ≤ level) := by
    rw [h.ptn, h.queue]
  change Equiv (renamingOf p) level
    (if s.ptn[s.queue[pos]!]! ≤ level then splitSingleton (.ofGraph G) level s.queue[pos]! a
      else splitNontrivial (.ofGraph G) level s.queue[pos]! a)
    (if t.ptn[t.queue[pos]!]! ≤ level then splitSingleton (.ofGraph H) level t.queue[pos]! b
      else splitNontrivial (.ofGraph H) level t.queue[pos]! b)
  simp only [htest]
  by_cases hsingle : s.ptn[s.queue[pos]!]! ≤ level
  · simp only [ite_eq_left hsingle, ← h.queue]
    apply he.singleton G H p hiso ha hb _ hc.1
    exact ⟨by omega, hc.2.1.2.1, by intro q hq hu; omega,
      by simpa only [a, RefineSt.hash, Nat.add_sub_cancel] using hsingle⟩
  · simp only [ite_eq_right hsingle, ← h.queue]
    exact he.nontrivial G H p hiso ha hb _ _ hc.2.1 (by omega)

end Hex.GraphIso.Nauty.Sparse.RefineSt.Equiv
