/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CertState

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt.Valid

variable {n level : Nat} {s : RefineSt n}

/-- The actual singleton branch preserves the equitability certificate,
including swap/pop removal and hashing of the selected splitter. -/
theorem singleton_cert (h : Valid level s) (G : Hex.SparseGraph n) (pos : Nat)
    (hp : pos < s.queue.size) (hsplit : s.ptn[s.queue[pos]!]! ≤ level)
    (hinv : CertInv (Graph.context G) level s.toPartition) :
    let r := ({ s with
      active := s.active.erase s.queue[pos]!,
      queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash s.queue[pos]!
    CertInv (Graph.context G) level (splitSingleton (.ofGraph G) level s.queue[pos]! r).toPartition := by
  let r := ({ s with
      active := s.active.erase s.queue[pos]!,
      queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash s.queue[pos]!
  have hr : Valid level r := (h.remove hp).hash _
  have hcell := h.queue_cell hp
  have hend : s.cellend[s.queue[pos]!]! = s.queue[pos]! := by
    by_cases he : s.cellend[s.queue[pos]!]! = s.queue[pos]!
    · exact he
    · have := hcell.2.1.2.2.1 s.queue[pos]! (Nat.le_refl _) (by omega)
      omega
  have hce := h.index.end_eq h.size h.closed hcell.1 (h.queue.starts _ (h.queue_mem hp))
  have hout := hr.singleton G _ hcell.1
  have hstep : Step level s (splitSingleton (.ofGraph G) level s.queue[pos]! r) :=
    ⟨hout.2.cuts, hout.2.cells⟩
  apply cert_transport G s.queue[pos]! h hout.1 hstep hcell.1 (h.queue_mem hp) _ _ hinv
  · exact splitSingleton_active G level _ r hr.lab hr.size hr.closed hcell.1 hr.index
      ⟨hr.scratch.marks_size, hr.scratch.marks_le⟩ ⟨hr.scratch.vmarks_size, hr.scratch.vmarks_le⟩
  · have he : cellEnd s.ptn level s.queue[pos]! = s.queue[pos]! := hce.symm.trans hend
    rw [he]
    exact hr.singleton_const G _ hcell.1

/-- The actual nontrivial branch preserves the equitability certificate,
including the exact queue removal and largest-fragment activation choices. -/
theorem nontrivial_cert (h : Valid level s) (G : Hex.SparseGraph n) (pos : Nat)
    (hp : pos < s.queue.size) (hinv : CertInv (Graph.context G) level s.toPartition) :
    let r := ({ s with
      active := s.active.erase s.queue[pos]!,
      queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash s.queue[pos]!
    CertInv (Graph.context G) level (splitNontrivial (.ofGraph G) level s.queue[pos]! r).toPartition := by
  let r := ({ s with
      active := s.active.erase s.queue[pos]!,
      queue := (s.queue.setIfInBounds pos s.queue[s.queue.size - 1]!).pop } : RefineSt n).hash s.queue[pos]!
  have hr : Valid level r := (h.remove hp).hash _
  have hcell := h.queue_cell hp
  have hbound : s.queue[pos]! + (s.cellend[s.queue[pos]!]! + 1 - s.queue[pos]!) ≤ n := by omega
  have hce := h.index.end_eq h.size h.closed hcell.1 (h.queue.starts _ (h.queue_mem hp))
  have hout := hr.nontrivial G _ _ hcell.2.1 hbound
  have hstep : Step level s (splitNontrivial (.ofGraph G) level s.queue[pos]! r) :=
    ⟨hout.2.cuts, hout.2.cells⟩
  apply cert_transport G s.queue[pos]! h hout.1 hstep hcell.1 (h.queue_mem hp) _ _ hinv
  · exact splitNontrivial_active G level _ _ r hr.lab hr.size hr.closed hr.index hcell.2.1 hbound
      ⟨hr.scratch.marks_size, hr.scratch.marks_le⟩ hr.scratch.hits_size
  · rw [← hce]
    exact hr.nontrivial_const G _ _ hcell.2.1 hbound

end Hex.GraphIso.Nauty.Sparse.RefineSt.Valid
