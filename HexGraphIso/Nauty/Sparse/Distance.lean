/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GraphProps

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A walk of a specified length in the native sparse graph. -/
inductive Walk (G : Hex.SparseGraph n) (root : Fin n) : Fin n → Nat → Prop
  | nil : Walk G root root 0
  | step {u v : Fin n} {length : Nat} :
      Walk G root u length → G.adj u v = true → Walk G root v (length + 1)

theorem Walk.map {G H : Hex.SparseGraph n} {root v : Fin n} {length : Nat}
    (f : Fin n → Fin n) (ha : ∀ u v, G.adj u v = true → H.adj (f u) (f v) = true)
    (h : Walk G root v length) : Walk H (f root) (f v) length := by
  induction h with
  | nil => exact .nil
  | step _ he ih => exact .step ih (ha _ _ he)

theorem Walk.relabel {G : Hex.SparseGraph n} {root v : Fin n} {length : Nat} (p : Perm n) :
    Walk (G.relabel p) root v length ↔ Walk G (p.get root) (p.get v) length := by
  constructor
  · exact Walk.map p.get (fun u v h => by simpa using h)
  · intro h
    have hm := h.map p.inv.get (H := G.relabel p) (fun u v h => by simpa using h)
    simpa using hm

/-- Shortest-path values with `n` representing exactly the unreachable
vertices. This contract includes both an attaining walk and minimality. -/
structure Distances (G : Hex.SparseGraph n) (root : Fin n) (dist : Array Nat) : Prop where
  size_eq : dist.size = n
  bound : ∀ v : Fin n, dist[v.val]! ≤ n
  sound : ∀ v : Fin n, dist[v.val]! < n → Walk G root v dist[v.val]!
  complete : ∀ {v length}, Walk G root v length → dist[v.val]! < n ∧ dist[v.val]! ≤ length

namespace Distances

theorem root_eq {G : Hex.SparseGraph n} {root : Fin n} {dist : Array Nat}
    (h : Distances G root dist) : dist[root.val]! = 0 := by
  have hr := h.complete .nil
  omega

theorem unreachable {G : Hex.SparseGraph n} {root v : Fin n} {dist : Array Nat}
    (h : Distances G root dist) : dist[v.val]! = n ↔ ¬∃ length, Walk G root v length := by
  constructor
  · rintro he ⟨length, hw⟩
    have hb := h.complete hw
    omega
  · intro hw
    have hb := h.bound v
    by_cases hd : dist[v.val]! < n
    · exact False.elim (hw ⟨_, h.sound v hd⟩)
    · omega

theorem unique {G : Hex.SparseGraph n} {root : Fin n} {a b : Array Nat}
    (ha : Distances G root a) (hb : Distances G root b) : a = b := by
  apply Array.ext
  · exact ha.size_eq.trans hb.size_eq.symm
  · intro i hi hj
    have hin : i < n := by rw [ha.size_eq] at hi; exact hi
    have hba := ha.bound ⟨i, hin⟩
    have hbb := hb.bound ⟨i, hin⟩
    change a[i]! ≤ n at hba
    change b[i]! ≤ n at hbb
    by_cases hia : a[i]! < n
    · have hab := hb.complete (ha.sound ⟨i, hin⟩ hia)
      have hba := ha.complete (hb.sound ⟨i, hin⟩ hab.1)
      rw [getElem!_pos a i hi, getElem!_pos b i hj] at *
      omega
    · have hae : a[i]! = n := by omega
      have hau := (ha.unreachable (v := ⟨i, hin⟩)).mp hae
      have hbu := (hb.unreachable (v := ⟨i, hin⟩)).mpr hau
      rw [getElem!_pos a i hi, getElem!_pos b i hj] at *
      omega

/-- The final BFS obligations imply shortest paths: discovered vertices
have attaining walks and are closed under adjacency, and each edge increases
the assigned value by at most one. -/
theorem of_edges {G : Hex.SparseGraph n} {root : Fin n} {dist : Array Nat}
    (hsize : dist.size = n) (hbound : ∀ v : Fin n, dist[v.val]! ≤ n)
    (hroot : dist[root.val]! = 0)
    (hsound : ∀ v : Fin n, dist[v.val]! < n → Walk G root v dist[v.val]!)
    (hedge : ∀ u v : Fin n, dist[u.val]! < n → G.adj u v = true →
      dist[v.val]! < n ∧ dist[v.val]! ≤ dist[u.val]! + 1) : Distances G root dist := by
  refine ⟨hsize, hbound, hsound, ?_⟩
  intro v length hw
  induction hw with
  | nil => rw [hroot]; exact ⟨by have := root.isLt; omega, Nat.le_refl _⟩
  | step hw hadj ih =>
    have he := hedge _ _ ih.1 hadj
    exact ⟨he.1, by omega⟩

end Distances

end Hex.GraphIso.Nauty.Sparse
