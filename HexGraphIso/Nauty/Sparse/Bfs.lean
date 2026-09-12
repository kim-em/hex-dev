/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Queue

public section

namespace Hex.GraphIso.Nauty.Sparse

set_option maxHeartbeats 800000

/-- BFS queue invariants together with attaining walks and the completed
rows' edge inequalities. -/
structure Bfs (G : Hex.SparseGraph n) (root : Fin n)
    (dist queue : Array Nat) (head tail : Nat) : Prop extends Queue n dist queue head tail where
  root_eq : dist[root.val]! = 0
  sound : ∀ v, (hv : v < n) → dist[v]! < n → Walk G root ⟨v, hv⟩ dist[v]!
  edges : ∀ i, (hi : i < head) → ∀ v : Fin n,
    G.adj ⟨queue[i]!, vertex i (Nat.lt_of_lt_of_le hi head_le)⟩ v = true →
      dist[v.val]! < n ∧ dist[v.val]! ≤ dist[queue[i]!]! + 1

namespace Bfs

theorem initial (G : Hex.SparseGraph n) (root : Fin n) :
    Bfs G root ((Array.replicate n n).set! root.val 0)
      ((Array.replicate n 0).set! 0 root.val) 0 1 := by
  refine ⟨Queue.initial root, ?_, ?_, ?_⟩
  · exact Array.getElem!_set!_self _ _ _ (by simp)
  · intro v hv hd
    rw [Queue.set_read _ _ _ _ (by simpa),
      getElem!_pos (Array.replicate n n) v (by simpa), Array.getElem_replicate] at hd
    split at hd
    · next he =>
      have he' : (⟨v, hv⟩ : Fin n) = root := Fin.ext he.symm
      rw [show ((Array.replicate n n).set! root.val 0)[v]! = 0 by
        rw [← he]; exact Array.getElem!_set!_self _ _ _ (by simp)]
      rw [he']
      exact .nil
    · omega
  · intro i hi
    omega

theorem add {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat} {head tail : Nat}
    (h : Bfs G root dist queue head tail) (hh : head < tail) (v : Fin n)
    (hd : dist[v.val]! = n) (hn : dist[queue[head]!]! + 1 < n)
    (ha : G.adj ⟨queue[head]!, h.vertex head hh⟩ v = true) :
    Bfs G root (dist.set! v.val (dist[queue[head]!]! + 1))
      (queue.set! tail v.val) head (tail + 1) := by
  have hds := h.dist_size
  have hread (w : Nat) (hw : dist[w]! < n) :
      (dist.set! v.val (dist[queue[head]!]! + 1))[w]! = dist[w]! := by
    apply Array.getElem!_set!_ne
    intro he
    rw [← he, hd] at hw
    omega
  have hqueue (i : Nat) (hi : i < tail) : (queue.set! tail v.val)[i]! = queue[i]! :=
    Array.getElem!_set!_ne _ _ _ _ (by omega)
  refine ⟨h.toQueue.add hh v.isLt hd hn, ?_, ?_, ?_⟩
  · rw [hread _ (by rw [h.root_eq]; have := root.isLt; omega), h.root_eq]
  · intro w hw hfinite
    by_cases he : v.val = w
    · have he' : (⟨w, hw⟩ : Fin n) = v := Fin.ext he.symm
      have heval : (dist.set! v.val (dist[queue[head]!]! + 1))[w]! =
          dist[queue[head]!]! + 1 := by
        rw [← he, Array.getElem!_set!_self _ _ _ (by have := v.isLt; omega)]
      rw [heval, he']
      exact .step (h.sound _ (h.vertex head hh) (h.toQueue.finite hh)) ha
    · rw [Array.getElem!_set!_ne _ _ _ _ he] at hfinite ⊢
      exact h.sound w hw hfinite
  · intro i hi w ha
    have hit : i < tail := by have := h.head_le; omega
    have ha' : G.adj ⟨queue[i]!, h.vertex i hit⟩ w = true := by
      simpa only [hqueue i hit] using ha
    have he := h.edges i hi w ha'
    rw [hqueue i hit, hread _ (h.toQueue.finite hit), hread _ he.1]
    exact he

theorem advance {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat} {head tail : Nat}
    (h : Bfs G root dist queue head tail) (hh : head < tail)
    (he : ∀ v : Fin n, G.adj ⟨queue[head]!, h.vertex head hh⟩ v = true →
      dist[v.val]! < n ∧ dist[v.val]! ≤ dist[queue[head]!]! + 1) :
    Bfs G root dist queue (head + 1) tail := by
  refine ⟨h.toQueue.advance hh, h.root_eq, h.sound, ?_⟩
  intro i hi v ha
  by_cases hh' : i < head
  · exact h.edges i hh' v ha
  · have : i = head := by omega
    subst i
    exact he v ha

/-- Both executable stopping conditions produce shortest paths. If the
queue is full, its distance band covers the unprocessed rows as well. -/
theorem complete {G : Hex.SparseGraph n} {root : Fin n} {dist queue : Array Nat} {head tail : Nat}
    (h : Bfs G root dist queue head tail) (hdone : n ≤ tail ∨ tail ≤ head) :
    Distances G root dist := by
  apply Distances.of_edges h.dist_size (fun v => h.bound v.val v.isLt) h.root_eq
    (fun v hv => h.sound v.val v.isLt hv)
  intro u v hu ha
  obtain ⟨i, hi, hiu⟩ := (h.found u.val u.isLt).mp hu
  by_cases hip : i < head
  · have hui : (⟨queue[i]!, h.vertex i hi⟩ : Fin n) = u := Fin.ext hiu
    simpa only [hiu] using h.edges i hip v (by simpa only [hui] using ha)
  · have htail : tail = n := by have := h.tail_le; omega
    have hv : dist[v.val]! < n := by
      by_cases hv : dist[v.val]! < n
      · exact hv
      · have he : dist[v.val]! = n := by have := h.bound v.val v.isLt; omega
        have hr := h.toQueue.room v.isLt he
        omega
    obtain ⟨j, hj, hjv⟩ := (h.found v.val v.isLt).mp hv
    refine ⟨hv, ?_⟩
    simpa only [hiu, hjv] using h.band i j (by omega) hi hj

end Bfs

end Hex.GraphIso.Nauty.Sparse
