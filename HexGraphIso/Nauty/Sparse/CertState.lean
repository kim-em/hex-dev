/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SplitterConst
public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Equitable.Step

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt

/-- The partition fields observed by the shared certificate algebra. This
projection is confined to proofs and invokes no dense refinement routine. -/
@[expose] def toPartition (s : RefineSt n) : Nauty.RefineSt n := {
  lab := s.lab, ptn := s.ptn, active := s.active, numcells := s.numcells
  hint := 0, maxpos := 0, longcode := s.longcode }

variable {n level : Nat} {s t : RefineSt n}

theorem Valid.stOk (h : Valid level s) : StOk n level s.toPartition := by
  have hs : s.lab.size = n := by simpa using h.lab.length_eq
  exact ⟨hs, fun i hi => perm_bound h.lab (by change i < s.lab.size at hi; omega), h.size,
    by simpa only [toPartition, h.size] using h.closed⟩

theorem Valid.starts (h : Valid level s) : StartsOk level s.toPartition :=
  h.queue.starts

theorem Valid.injective (h : Valid level s) : LabInj s.lab n :=
  fun _ _ hi hj he => perm_injective h.lab hi hj he

theorem Valid.queue_mem (h : Valid level s) (hp : pos < s.queue.size) :
    s.active.mem s.queue[pos]! = true := by
  apply (h.queue.set.mem _).mp
  simpa only [getElem!_pos s.queue pos hp] using s.queue.getElem_mem_toList hp

theorem Step.refInv (h : Step level s t) (hs : Valid level s) (ht : Valid level t) :
    RefInv level s.lab s.ptn t.toPartition := by
  have hsl : s.lab.size = n := by simpa using hs.lab.length_eq
  have htl : t.lab.size = n := by simpa using ht.lab.length_eq
  refine ⟨htl.trans hsl.symm, h.cuts.size, ?_, ?_⟩
  · intro q hq
    change t.ptn[q]! ≤ level
    rw [h.cuts.closed q hq]
    exact hq
  · intro a len hc
    exact (h.cells a len hc).symm

/-- Sparse passes preserve the shared equitability certificate once their
proved native count and activation properties are supplied. -/
theorem cert_transport (G : Hex.SparseGraph n) (split : Nat)
    (hs : Valid level s) (ht : Valid level t) (hstep : Step level s t)
    (hb : split < n) (hm : s.active.mem split = true)
    (ha : Activation n level s.ptn t.ptn (s.active.erase split) t.active)
    (hc : ∀ a len, IsCell t.ptn level a len → a + len ≤ n →
      ConstOn (Graph.context G) (worksetOf n s.lab split (cellEnd s.ptn level split)) (segN t.lab a len))
    (hinv : CertInv (Graph.context G) level s.toPartition) :
    CertInv (Graph.context G) level t.toPartition := by
  apply certInv_transport hs.stOk ht.stOk hs.injective hs.starts hm hb
    (hstep.refInv hs ht) hc _ hinv
  intro p hp
  change p ∈ cells s.ptn level n at hp
  have hs' := hs.size
  have hend : s.ptn[s.ptn.size - 1]! ≤ level := by simpa only [hs.size] using hs.closed
  have hcell := cells_isCell (by omega : n ≤ s.ptn.size) hend p hp
  have hlast := cells_end_lt_of_end (by omega : n ≤ s.ptn.size) hend hs.closed p hp
  have hfirst := cells_le p hp
  have hactive := ha p.1 (p.2 + 1 - p.1) hcell (by omega)
  refine ⟨?_, ?_⟩
  · intro hm hn u hu hu' hstart
    change s.active.mem p.1 = true at hm
    apply hactive.all ?_ u hu (by omega) hstart
    simp only [VSet.mem_erase, hm, beq_eq_false_iff_ne.mpr (Ne.symm hn),
      Bool.not_false, Bool.and_true]
  · intro _
    obtain ⟨w, hw⟩ := hactive.one
    exact ⟨w, fun u hu hu' hstart hn => hw u hu (by omega) hstart hn⟩

end Hex.GraphIso.Nauty.Sparse.RefineSt
