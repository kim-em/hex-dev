/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Bfs

public section

namespace Hex.GraphIso.Nauty.Sparse

set_option maxHeartbeats 800000

/-- State of one packed adjacency scan. The queue head is advanced only
after all these edge obligations have been discharged. -/
structure Scan (G : Hex.SparseGraph n) (root : Fin n) (dist queue : Array Nat)
    (head tail current next : Nat) (seen : List Nat) : Prop extends Bfs G root dist queue head tail where
  head_lt : head < tail
  head_eq : queue[head]! = current
  next_eq : dist[current]! + 1 = next
  next_lt : next < n
  visited : ∀ e ∈ seen,
    dist[(Graph.ofGraph G).neighbor e]! < n ∧ dist[(Graph.ofGraph G).neighbor e]! ≤ next

namespace Scan

theorem current_lt {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat}
    {head tail current next : Nat} {seen : List Nat}
    (h : Scan G root dist queue head tail current next seen) : current < n := by
  rw [← h.head_eq]
  exact h.vertex head h.head_lt

theorem current_finite {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat}
    {head tail current next : Nat} {seen : List Nat}
    (h : Scan G root dist queue head tail current next seen) : dist[current]! < n := by
  rw [← h.head_eq]
  exact h.toQueue.finite h.head_lt

theorem initial {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat} {head tail : Nat}
    (h : Bfs G root dist queue head tail) (hh : head < tail) (ht : tail < n) :
    Scan G root dist queue head tail queue[head]! (dist[queue[head]!]! + 1) [] := by
  refine ⟨h, hh, rfl, rfl, ?_, by simp⟩
  have hi := h.index head hh
  omega

theorem add {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat}
    {head tail current next e : Nat} {seen : List Nat}
    (h : Scan G root dist queue head tail current next seen)
    (hlo : G.offsets[current]! ≤ e) (hhi : e < G.offsets[current + 1]!)
    (hd : dist[(Graph.ofGraph G).neighbor e]! = n) :
    Scan G root (dist.set! ((Graph.ofGraph G).neighbor e) next)
      (queue.set! tail ((Graph.ofGraph G).neighbor e)) head (tail + 1) current next (seen ++ [e]) := by
  have he := G.edge_lt (i := ⟨current, h.current_lt⟩) hhi
  let v := G.neighbors[e]'he
  have hv : (Graph.ofGraph G).neighbor e = v.val := Graph.neighbor_ofGraph G e he
  have hadj : G.adj ⟨queue[head]!, h.vertex head h.head_lt⟩ v = true := by
    have hi : (⟨queue[head]!, h.vertex head h.head_lt⟩ : Fin n) = ⟨current, h.current_lt⟩ :=
      Fin.ext h.head_eq
    rw [hi, ← Hex.SparseGraph.mem_nbrs]
    exact G.edge_mem ⟨current, h.current_lt⟩ hlo hhi
  have hnext : dist[queue[head]!]! + 1 = next := by rw [h.head_eq, h.next_eq]
  have hbfs := h.toBfs.add h.head_lt v (by simpa only [hv] using hd)
    (by rw [hnext]; exact h.next_lt) hadj
  rw [hnext, ← hv] at hbfs
  have hds := h.dist_size
  have hvn : (Graph.ofGraph G).neighbor e < n := by rw [hv]; exact v.isLt
  have hread (w : Nat) (hw : dist[w]! < n) :
      (dist.set! ((Graph.ofGraph G).neighbor e) next)[w]! = dist[w]! := by
    apply Array.getElem!_set!_ne
    intro heq
    rw [← heq, hd] at hw
    omega
  refine ⟨hbfs, by have := h.head_lt; omega, ?_, ?_, h.next_lt, ?_⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ (by have := h.head_lt; omega), h.head_eq]
  · rw [hread _ h.current_finite, h.next_eq]
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · rw [hread _ (h.visited j hj).1]
      exact h.visited j hj
    · have : j = e := by simpa using hj
      subst j
      rw [Array.getElem!_set!_self _ _ _ (by omega)]
      exact ⟨h.next_lt, Nat.le_refl _⟩

theorem keep {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat}
    {head tail current next e : Nat} {seen : List Nat}
    (h : Scan G root dist queue head tail current next seen)
    (hhi : e < G.offsets[current + 1]!)
    (hd : dist[(Graph.ofGraph G).neighbor e]! ≠ n) :
    Scan G root dist queue head tail current next (seen ++ [e]) := by
  have hv := Graph.neighbor_lt G ⟨current, h.current_lt⟩ hhi
  have hf : dist[(Graph.ofGraph G).neighbor e]! < n := by
    have hb := h.bound _ hv
    omega
  obtain ⟨j, hj, hjv⟩ := (h.found _ hv).mp hf
  have hle := h.band head j (Nat.le_refl _) h.head_lt hj
  rw [hjv, h.head_eq, h.next_eq] at hle
  refine { h with visited := ?_ }
  intro k hk
  rcases List.mem_append.mp hk with hk | hk
  · exact h.visited k hk
  · have : k = e := by simpa using hk
    subst k
    exact ⟨hf, hle⟩

theorem finish {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat}
    {head tail current next : Nat}
    (h : Scan G root dist queue head tail current next
      (List.range' G.offsets[current]! (G.offsets[current + 1]! - G.offsets[current]!))) :
    Bfs G root dist queue (head + 1) tail := by
  apply h.toBfs.advance h.head_lt
  intro v ha
  have hi : (⟨queue[head]!, h.vertex head h.head_lt⟩ : Fin n) = ⟨current, h.current_lt⟩ :=
    Fin.ext h.head_eq
  rw [hi, ← Hex.SparseGraph.mem_nbrs] at ha
  obtain ⟨e, hlo, hhi, hev⟩ := G.mem_edge ha
  change G.offsets[current]! ≤ e at hlo
  change e < G.offsets[current + 1]! at hhi
  have he := G.edge_lt (i := ⟨current, h.current_lt⟩) hhi
  have hv : (Graph.ofGraph G).neighbor e = v.val := by
    rw [Graph.neighbor_ofGraph G e he]
    rw [getElem?_pos G.neighbors e he, Option.some.injEq] at hev
    exact congrArg Fin.val hev
  have hh := h.visited e (by simp only [List.mem_range'_1]; omega)
  rw [hv, ← h.next_eq, ← h.head_eq] at hh
  exact hh

end Scan

end Hex.GraphIso.Nauty.Sparse
