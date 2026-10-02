/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DistanceRun
public import HexGraphIso.Nauty.Sparse.DistanceAdj
public import HexGraphIso.Nauty.Sparse.PassCert

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Completed distance classes stabilize the captured singleton splitter. -/
theorem DistanceState.constOn {n level split : Nat} {s t : RefineSt n}
    (h : DistanceState level s t n) (hs : RefineSt.Valid level s)
    (G : Hex.SparseGraph n) (root : Fin n) (hd : Distances G root s.hits)
    (hb : split < n) (hr : s.lab[split]! = root.val) :
    ∀ a len, IsCell t.ptn level a len → a + len ≤ n →
      ConstOn (Graph.context G) (worksetOf n s.lab split split) (segN t.lab a len) := by
  intro a len ha hab
  apply Graph.constOn_workset G s.lab t.lab hs.lab h.valid.lab (Nat.le_refl _) hb hab
  intro q r hq hq' hr' hr''
  have he := h.constant.done a len ha hab q r hq hq' hr' hr''
  have hvq := perm_bound h.valid.lab (i := q) (by omega)
  have hvr := perm_bound h.valid.lab (i := r) (by omega)
  simpa only [Nat.add_sub_cancel_left, List.range'_succ, List.range'_zero,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] using
      hd.count_congr ⟨t.lab[q]!, hvq⟩ ⟨t.lab[r]!, hvr⟩ he

namespace RefineSt.Valid

variable {n level : Nat} {s : RefineSt n}

/-- Removing the sole queued splitter and installing native BFS distances
preserves all structural state invariants. -/
theorem distance_start (h : Valid level s) (G : Hex.SparseGraph n) (hq : s.queue.size = 1) :
    Valid level ({ s with
      queue := #[], active := s.active.erase s.queue[0]!
      hits := distvals (.ofGraph G) s.lab[s.queue[0]!]! } : RefineSt n) := by
  have hp : 0 < s.queue.size := by omega
  let r : RefineSt n := { s with
    queue := #[], active := s.active.erase s.queue[0]!
    hits := distvals (.ofGraph G) s.lab[s.queue[0]!]! }
  have hqr := h.queue.remove hp
  have heq : (s.queue.setIfInBounds 0 s.queue[s.queue.size - 1]!).pop = #[] := by
    apply Array.eq_empty_of_size_eq_zero
    simp only [Array.size_pop, Array.size_setIfInBounds, hq]
  rw [heq] at hqr
  have hr : Valid level r := ⟨h.lab, h.size, h.closed, h.index,
    ⟨h.scratch.starts_size, h.scratch.ends_size, distvals_size _ _,
      h.scratch.marks_size, h.scratch.vmarks_size, h.scratch.marks_le, h.scratch.vmarks_le⟩, hqr⟩
  exact hr

/-- Any completed execution of the distance-cell scan transports the
incoming certificate, using the proved native distance semantics. -/
theorem distance_finish (h : Valid level s) (G : Hex.SparseGraph n)
    (hq : s.queue.size = 1) (hsplit : s.ptn[s.queue[0]!]! ≤ level)
    (hinv : CertInv (Graph.context G) level s.toPartition) {t : RefineSt n}
    (ht : DistanceState level ({ s with
      queue := #[], active := s.active.erase s.queue[0]!
      hits := distvals (.ofGraph G) s.lab[s.queue[0]!]! } : RefineSt n) t n) :
    CertInv (Graph.context G) level t.toPartition := by
  have hp : 0 < s.queue.size := by omega
  have hcell := h.queue_cell hp
  have hroot := perm_bound h.lab hcell.1
  have hd := distvals_correct G ⟨s.lab[s.queue[0]!]!, hroot⟩
  have hr := h.distance_start G hq
  have hstep : Step level s _ := ⟨ht.step.cuts, ht.step.cells⟩
  apply cert_transport G s.queue[0]! h ht.valid hstep hcell.1 (h.queue_mem hp) ht.active _ hinv
  have hend : s.cellend[s.queue[0]!]! = s.queue[0]! := by
    by_cases he : s.cellend[s.queue[0]!]! = s.queue[0]!
    · exact he
    · have := hcell.2.1.2.2.1 s.queue[0]! (Nat.le_refl _) (by omega)
      omega
  have hce := h.index.end_eq h.size h.closed hcell.1 (h.queue.starts _ (h.queue_mem hp))
  rw [hce.symm.trans hend]
  exact ht.constOn hr G _ hd hcell.1 rfl

/-- The literal shallow distance branch preserves the equitability
certificate. Its extra depth and size guards require no additional
semantic assumption. -/
theorem distance_cert (h : Valid level s) (G : Hex.SparseGraph n)
    (hq : s.queue.size = 1) (hsplit : s.ptn[s.queue[0]!]! ≤ level)
    (hinv : CertInv (Graph.context G) level s.toPartition) :
    let t : RefineSt n := Id.run do
      let split := s.queue[0]!
      let mut state := { s with
        queue := #[], active := s.active.erase split
        hits := distvals (.ofGraph G) s.lab[split]! }
      let mut first := 0
      for _ in [0:n] do
        if first >= n then break
        let last := state.cellend[first]!
        if first < last then state := splitCounts level first true state
        first := last + 1
      return state
    CertInv (Graph.context G) level t.toPartition := by
  have hp : 0 < s.queue.size := by omega
  have hcell := h.queue_cell hp
  have hroot := perm_bound h.lab hcell.1
  let r : RefineSt n := { s with
    queue := #[], active := s.active.erase s.queue[0]!
    hits := distvals (.ofGraph G) s.lab[s.queue[0]!]! }
  have hd := distvals_correct G ⟨s.lab[s.queue[0]!]!, hroot⟩
  have hr : Valid level r := h.distance_start G hq
  exact h.distance_finish G hq hsplit hinv (split_distances level r hr (fun v hv => hd.bound ⟨v, hv⟩))

end RefineSt.Valid
end Hex.GraphIso.Nauty.Sparse
