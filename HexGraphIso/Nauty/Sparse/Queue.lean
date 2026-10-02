/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Distance

public section

namespace Hex.GraphIso.Nauty.Sparse

set_option maxHeartbeats 800000

/-- The allocated BFS queue contains every discovered vertex exactly once.
Its distance order and frontier band justify both append operations and the
early exit when all vertices have been discovered. -/
structure Queue (n : Nat) (dist queue : Array Nat) (head tail : Nat) : Prop where
  dist_size : dist.size = n
  queue_size : queue.size = n
  head_le : head ≤ tail
  tail_le : tail ≤ n
  vertex : ∀ i, i < tail → queue[i]! < n
  injective : ∀ i j, i < tail → j < tail → queue[i]! = queue[j]! → i = j
  bound : ∀ v, v < n → dist[v]! ≤ n
  found : ∀ v, v < n → (dist[v]! < n ↔ ∃ i, i < tail ∧ queue[i]! = v)
  index : ∀ i, i < tail → dist[queue[i]!]! ≤ i
  sorted : ∀ i j, i ≤ j → j < tail → dist[queue[i]!]! ≤ dist[queue[j]!]!
  band : ∀ i j, head ≤ i → i < tail → j < tail → dist[queue[j]!]! ≤ dist[queue[i]!]! + 1

namespace Queue

theorem set_read (a : Array Nat) (i value j : Nat) (hj : j < a.size) :
    (a.set! i value)[j]! = if i = j then value else a[j]! := by
  by_cases he : i = j
  · subst i
    rw [Array.getElem!_set!_self _ _ _ hj, ite_eq_left rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ he, ite_eq_right he]

theorem finite {dist queue : Array Nat} {head tail : Nat}
    (h : Queue n dist queue head tail) {i : Nat} (hi : i < tail) :
    dist[queue[i]!]! < n := (h.found _ (h.vertex i hi)).mpr ⟨i, hi, rfl⟩

theorem fresh {dist queue : Array Nat} {head tail v : Nat}
    (h : Queue n dist queue head tail) (_hv : v < n) (hd : dist[v]! = n)
    {i : Nat} (hi : i < tail) : queue[i]! ≠ v := by
  intro he
  have hf := h.finite hi
  rw [he, hd] at hf
  omega

/-- An undiscovered vertex forces a free slot in the fixed queue. -/
theorem room {dist queue : Array Nat} {head tail v : Nat}
    (h : Queue n dist queue head tail) (hv : v < n) (hd : dist[v]! = n) : tail < n := by
  have htail := h.tail_le
  let seen := queue.toList.take tail
  have hlen : seen.length = tail := by simp [seen, h.queue_size, Nat.min_eq_left h.tail_le]
  have hnodup : seen.Nodup := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [seen, List.getElem_take, Array.getElem_toList]
    intro he
    have hi' : i < tail := by rw [hlen] at hi; exact hi
    have hj' : j < tail := by rw [hlen] at hj; exact hj
    have he' : queue[i]! = queue[j]! := by
      rw [getElem!_pos queue i (by rw [h.queue_size]; omega),
        getElem!_pos queue j (by rw [h.queue_size]; omega)]
      exact he
    have := h.injective i j hi' hj' he'
    omega
  have hmem (w : Nat) (hw : w ∈ seen) : w < n ∧ w ≠ v := by
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
    have hi' : i < tail := by rw [hlen] at hi; exact hi
    have he' : queue[i]! = w := by
      simpa only [seen, List.getElem_take, Array.getElem_toList,
        getElem!_pos queue i (by rw [h.queue_size]; omega)] using he
    rw [← he']
    exact ⟨h.vertex i hi', h.fresh hv hd hi'⟩
  have hvnot : v ∉ seen := fun hm => (hmem v hm).2 rfl
  have hle := (List.nodup_cons.mpr ⟨hvnot, hnodup⟩).length_le_of_subset
    (l₂ := List.range n) (fun w hw => by
      rw [List.mem_range]
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hv
      · exact (hmem w hw).1)
  simp only [List.length_cons, List.length_range, hlen] at hle
  omega

theorem initial (root : Fin n) :
    Queue n ((Array.replicate n n).set! root.val 0)
      ((Array.replicate n 0).set! 0 root.val) 0 1 := by
  have hn : 0 < n := by have := root.isLt; omega
  have hzero : ((Array.replicate n 0).set! 0 root.val)[0]! = root.val :=
    Array.getElem!_set!_self _ _ _ (by simpa)
  have hroot : ((Array.replicate n n).set! root.val 0)[root.val]! = 0 :=
    Array.getElem!_set!_self _ _ _ (by simp)
  have hread (v : Nat) (hv : v < n) :
      ((Array.replicate n n).set! root.val 0)[v]! = if root.val = v then 0 else n := by
    rw [set_read _ _ _ _ (by simpa), getElem!_pos (Array.replicate n n) v (by simpa)]
    simp only [Array.getElem_replicate]
  constructor
  · simp
  · simp
  · omega
  · omega
  · intro i hi
    have : i = 0 := by omega
    subst i
    rw [hzero]
    exact root.isLt
  · intros; omega
  · intro v hv
    rw [hread v hv]
    split <;> omega
  · intro v hv
    rw [hread v hv]
    constructor
    · intro hd
      refine ⟨0, by omega, ?_⟩
      rw [hzero]
      split at hd <;> omega
    · rintro ⟨i, hi, he⟩
      have : i = 0 := by omega
      subst i
      rw [hzero] at he
      rw [ite_eq_left he]
      omega
  · intro i hi
    have : i = 0 := by omega
    subst i
    rw [hzero, hroot]
    exact Nat.le_refl _
  · intro i j hij hj
    have : i = j := by omega
    subst i
    exact Nat.le_refl _
  · intro i j _ hi hj
    have : i = j := by omega
    subst i
    omega

/-- Discovering an unseen neighbour appends it once and gives it the next
distance after the current head. The head stays fixed during its row scan. -/
theorem add {dist queue : Array Nat} {head tail v : Nat}
    (h : Queue n dist queue head tail) (hh : head < tail) (hv : v < n)
    (hd : dist[v]! = n) (hn : dist[queue[head]!]! + 1 < n) :
    Queue n (dist.set! v (dist[queue[head]!]! + 1)) (queue.set! tail v) head (tail + 1) := by
  have hroom := h.room hv hd
  have hdsize := h.dist_size
  have hqsize := h.queue_size
  have hqueue (i : Nat) (hi : i < tail) : (queue.set! tail v)[i]! = queue[i]! :=
    Array.getElem!_set!_ne _ _ _ _ (by omega)
  have hlast : (queue.set! tail v)[tail]! = v :=
    Array.getElem!_set!_self _ _ _ (by omega)
  have hvalue : (dist.set! v (dist[queue[head]!]! + 1))[v]! = dist[queue[head]!]! + 1 :=
    Array.getElem!_set!_self _ _ _ (by omega)
  have hdist (i : Nat) (hi : i < tail) :
      (dist.set! v (dist[queue[head]!]! + 1))[(queue.set! tail v)[i]!]! = dist[queue[i]!]! := by
    rw [hqueue i hi, Array.getElem!_set!_ne _ _ _ _ (h.fresh hv hd hi).symm]
  have htail : (dist.set! v (dist[queue[head]!]! + 1))[(queue.set! tail v)[tail]!]! =
      dist[queue[head]!]! + 1 := by rw [hlast, hvalue]
  refine ⟨by simpa, by simpa, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    by_cases he : i = tail
    · rw [he, hlast]; exact hv
    · rw [hqueue i (by omega)]; exact h.vertex i (by omega)
  · intro i j hi hj heq
    by_cases hi' : i = tail
    · subst i
      by_cases hj' : j = tail
      · exact hj'.symm
      · rw [hlast, hqueue j (by omega)] at heq
        exact False.elim (h.fresh hv hd (by omega) heq.symm)
    · by_cases hj' : j = tail
      · subst j
        rw [hqueue i (by omega), hlast] at heq
        exact False.elim (h.fresh hv hd (by omega) heq)
      · rw [hqueue i (by omega), hqueue j (by omega)] at heq
        exact h.injective i j (by omega) (by omega) heq
  · intro w hw
    rw [set_read _ _ _ _ (by omega)]
    split
    · omega
    · exact h.bound w hw
  · intro w hw
    by_cases he : w = v
    · subst w
      rw [hvalue]
      exact ⟨fun _ => ⟨tail, by omega, hlast⟩, fun _ => hn⟩
    · rw [Array.getElem!_set!_ne _ _ _ _ (fun hvw => he hvw.symm), h.found w hw]
      constructor
      · rintro ⟨i, hi, hiw⟩
        exact ⟨i, by omega, by rw [hqueue i hi, hiw]⟩
      · rintro ⟨i, hi, hiw⟩
        by_cases hi' : i = tail
        · rw [hi', hlast] at hiw
          exact False.elim (he hiw.symm)
        · exact ⟨i, by omega, by rwa [hqueue i (by omega)] at hiw⟩
  · intro i hi
    by_cases he : i = tail
    · rw [he, htail]
      have hi := h.index head hh
      omega
    · rw [hdist i (by omega)]
      exact h.index i (by omega)
  · intro i j hij hj
    by_cases hj' : j = tail
    · subst j
      by_cases hi' : i = tail
      · subst i; exact Nat.le_refl _
      · rw [hdist i (by omega), htail]
        exact h.band head i (Nat.le_refl _) hh (by omega)
    · rw [hdist i (by omega), hdist j (by omega)]
      exact h.sorted i j hij (by omega)
  · intro i j hhi hi hj
    by_cases hi' : i = tail
    · subst i
      by_cases hj' : j = tail
      · subst j; omega
      · rw [htail, hdist j (by omega)]
        have hj := h.band head j (Nat.le_refl _) hh (by omega)
        omega
    · by_cases hj' : j = tail
      · subst j
        rw [hdist i (by omega), htail]
        have hi := h.sorted head i hhi (by omega)
        omega
      · rw [hdist i (by omega), hdist j (by omega)]
        exact h.band i j hhi (by omega) (by omega)

/-- Completing one row advances the queue head without changing entries. -/
theorem advance {dist queue : Array Nat} {head tail : Nat}
    (h : Queue n dist queue head tail) (hh : head < tail) :
    Queue n dist queue (head + 1) tail :=
  { h with head_le := by omega
           band := fun i j hi hit hj => h.band i j (by omega) hit hj }

end Queue

end Hex.GraphIso.Nauty.Sparse
