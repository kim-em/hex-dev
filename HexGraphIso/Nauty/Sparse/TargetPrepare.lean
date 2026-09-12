/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetMap

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- The packed neighbour scan observes precisely the compact encoding of
its cached cell-index row. -/
theorem row_encode (G : Hex.SparseGraph n) (lab : Array Nat) (s : Scratch)
    (keys : List Nat) (raw : Array Nat) (h : MapPrefix n lab s.cellstart keys n raw)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (first : Nat) (hf : first < n) :
    ((List.range' G.offsets[lab[first]!]!
      (G.offsets[lab[first]! + 1]! - G.offsets[lab[first]!]!)).map
      (fun e => raw[(Graph.ofGraph G).neighbor e]!)) =
      (row (.ofGraph G) lab s first).map (encode keys n) := by
  have hv : lab[first]! < n := by
    rw [← Label.ofArray?_get hl first hf]
    exact (l.get ⟨first, hf⟩).isLt
  simp only [row, Graph.ofGraph, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro e he
  have hb := List.mem_range'_1.mp he
  have he' : e < G.offsets[lab[first]! + 1]! := by omega
  exact h.complete l hl ⟨_, Graph.neighbor_lt G ⟨lab[first]!, hv⟩ he'⟩

/-- The parallel size array gives the size of the cell at each compact index. -/
theorem sizes_get {sizes : Array Nat} {keys : List Nat} {degree : Nat → Nat}
    (h : sizes.toList = keys.map degree) {i : Nat} (hi : i < keys.length) :
    sizes[i]! = degree keys[i]! := by
  have hs : sizes.size = keys.length := by simpa using congrArg List.length h
  have hb : i < sizes.size := by omega
  have he := congrArg (fun xs => xs[i]!) h
  simpa only [Array.getElem!_toList, getElem!_pos (keys.map degree) i (by simpa using hi),
    List.getElem_map, getElem!_pos keys i hi] using he

/-- Translating compact indices commutes with each strict score comparison. -/
theorem select_map (f left right : Nat → Nat) (state : Nat × Nat) (i : Nat)
    (h : left i = right (f i)) :
    Prod.map f id (select left state i) = select right (Prod.map f id state) (f i) := by
  simp only [select, h, Prod.map, id_eq]
  split <;> rfl

/-- The translated best-so-far state follows the same ordered score fold. -/
theorem fold_map (f left right : Nat → Nat) (xs : List Nat) (state : Nat × Nat)
    (h : ∀ i ∈ xs, left i = right (f i)) :
    Prod.map f id (xs.foldl (select left) state) =
      (xs.map f).foldl (select right) (Prod.map f id state) := by
  induction xs generalizing state with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih _ (fun j hj => h j (by simp [hj])), select_map f left right state i (h i (by simp))]

/-- Every cell index read from a valid native row is listed or is the singleton sentinel. -/
theorem row_entries (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat) (s : Scratch)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (first : Nat) (hf : first < n) :
    ∀ k ∈ row (.ofGraph G) lab s first, k = n ∨ k ∈ nontrivial (cells ptn level n) := by
  have hv : lab[first]! < n := by
    rw [← Label.ofArray?_get hl first hf]
    exact (l.get ⟨first, hf⟩).isLt
  intro k hk
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
  have he' := List.mem_range'_1.mp he
  simp only [Graph.ofGraph] at he'
  have hb : e < G.offsets[lab[first]! + 1]! := by omega
  exact vertex_index hidx hs hend l hl ⟨_, Graph.neighbor_lt G ⟨lab[first]!, hv⟩ hb⟩

/-- Computing scores with compact ranks gives the same native partial-join score. -/
theorem encoded_score (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat) (s : Scratch)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend)
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (first : Nat) (hf : first < n) :
    let keys := nontrivial (cells ptn level n)
    (List.range keys.length).countP
      (Join.qualifies ((row (.ofGraph G) lab s first).map (encode keys n))
        (fun i => s.cellend[keys[i]!]! - keys[i]! + 1)) = score (.ofGraph G) lab s keys first := by
  dsimp only [score]
  apply scores_encode (degree := fun k => s.cellend[k]! - k + 1) (nodup ptn level n)
    (fun hm => Nat.lt_irrefl n (bound hs hend hm)) (length_le hs hend)
    (row_entries G lab ptn level s hidx hs hend l hl first hf)
    (fun _ _ => rfl)

end Hex.GraphIso.Nauty.Sparse.Target
