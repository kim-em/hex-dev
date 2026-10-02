/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GraphProps
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

private def Image (g : Graph n) (p : Array Nat) (i v : Nat) : Prop :=
  ∃ e, g.offsets[i]! ≤ e ∧ e < g.offsets[i + 1]! ∧ p[g.neighbor e]! = v

private def RowOk (g : Graph n) (p : Array Nat) (i : Nat) : Prop :=
  g.degree p[i]! = g.degree i ∧
    ∀ e, g.offsets[p[i]!]! ≤ e → e < g.offsets[p[i]! + 1]! →
      Image g p i (g.neighbor e)

private theorem range_cursor {s t i : Nat} {pref suff : List Nat}
    (h : List.range' s (t - s) = pref ++ i :: suff) :
    s ≤ i ∧ i < t ∧ i = s + pref.length := by
  have hi := List.mem_of_range'_eq_append_cons h
  have he := List.eq_of_range'_eq_append_cons h
  simp only [List.mem_range'_1] at *
  omega

private theorem isautom_rows (G : Hex.SparseGraph n) (p : Array Nat)
    (hp : ∀ i, i < n → p[i]! < n) :
    isautom (.ofGraph G) p = true ↔
      ∀ i, i < n → p[i]! ≠ i → RowOk (.ofGraph G) p i := by
  unfold isautom
  apply Id.of_wp_run_eq rfl (fun b : Bool => b = true ↔
    ∀ i, i < n → p[i]! ≠ i → RowOk (.ofGraph G) p i)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      (s.1 = none ∨ cursor.suffix = []) ∧
      (s.1 = none → s.2.size = n ∧
        (∀ v, v < n → s.2[v]! ≤ cursor.prefix.length) ∧
        ∀ i ∈ cursor.prefix, p[i]! ≠ i → RowOk (.ofGraph G) p i) ∧
      (∀ b, s.1 = some b → (b = true ↔
        ∀ i, i < n → p[i]! ≠ i → RowOk (.ofGraph G) p i))⌝
  | inv2 pref i suff he s marks hmove pi hdegree stamp hs => ⇓⟨cursor, marks⟩ => ⌜
      marks.size = n ∧ (∀ v, v < n → marks[v]! ≤ i + 1) ∧
      (∀ v, v < n → (marks[v]! = i + 1 ↔
        ∃ e ∈ cursor.prefix, p[(Graph.ofGraph G).neighbor e]! = v))⌝
  | inv3 pref i suff he s oldmarks hmove pi hdegree stamp hs marks hm => ⇓⟨cursor, r⟩ => ⌜
      (r.1 = none ∨ cursor.suffix = []) ∧
      (r.1 = none → ∀ e ∈ cursor.prefix, Image (.ofGraph G) p i ((Graph.ofGraph G).neighbor e)) ∧
      (∀ b, r.1 = some b → b = false ∧ ∃ e ∈ cursor.prefix,
        ¬Image (.ofGraph G) p i ((Graph.ofGraph G).neighbor e))⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, bne_iff_ne] at *

  all_goals simp_all
  case vc1.step.isTrue.isTrue =>
    rename_i pref i suff b marks pi hs hr hm hd
    have hi := range_cursor (s := 0) (t := n) hr
    exact ⟨i, hi.2.1, hm, fun h => hd h.1⟩
  case vc2.step =>
    rename_i hmark' hold hmark hr hmove hdeg he
    constructor
    · intro v hv
      have h := hmark.2.1 v hv
      rw [Array.getElem_setIfInBounds (by omega)]
      split <;> simp_all
    · intro v hv
      have h := hmark.2.2 v hv
      rw [Array.getElem_setIfInBounds (by omega)]
      split <;> simp_all
  case vc3.step.isTrue.isFalse.pre =>
    rename_i pref i suff b marks pi stamp hs' hs hr hm hd
    have hi := range_cursor (s := 0) (t := n) hr
    have hsize := (hs.2.1 hs.1).1
    constructor <;> intro v hv
    all_goals
      have h := (hs.2.1 hs.1).2.1 v hv
      rw [getElem!_pos b.2 v (by omega)] at h
      omega
  case vc4.step.isTrue =>
    rename_i hs ht hr hm hd hmarks he hmiss
    have hi := range_cursor (s := 0) (t := n) hr
    have hj := range_cursor he
    have hv := Graph.neighbor_lt G ⟨_, hp _ hi.2.1⟩ hj.2.1
    refine ⟨_, Or.inr (Or.inl rfl), ?_⟩
    intro himage
    obtain ⟨j, hlo, hhi, hval⟩ := himage
    apply hmiss
    apply (hmarks.2.2 _ hv).mpr
    exact ⟨j, ⟨hlo, by omega⟩, hval⟩
  case vc5.step.isFalse =>
    rename_i hs ht hr hm hd hmarks he hhit
    have hi := range_cursor (s := 0) (t := n) hr
    have hj := range_cursor he
    have hv := Graph.neighbor_lt G ⟨_, hp _ hi.2.1⟩ hj.2.1
    intro e he'
    rcases he' with he' | rfl
    · exact ht.2.1 ht.1 e he'
    · obtain ⟨j, ⟨hlo, hhi⟩, hval⟩ := (hmarks.2.2 _ hv).mp hhit
      exact ⟨j, hlo, by omega, hval⟩
  case vc7.step.isTrue.isFalse.post.success.post.success.h_1 =>
    rename_i hs hx hr hm hd hmarks hbad
    have hi := range_cursor (s := 0) (t := n) hr
    refine ⟨_, hi.2.1, hm, ?_⟩
    intro hrow
    obtain ⟨e, ⟨hlo, hhi⟩, he⟩ := hbad.2
    exact he (hrow.2 e hlo (by omega))
  case vc8.step.isTrue.isFalse.post.success.post.success.h_2 =>
    rename_i hmarks' hs hx hr hm hd hmarks hrow
    have hi := range_cursor (s := 0) (t := n) hr
    constructor
    · intro v hv
      have h := hmarks.2.1 v hv
      have hsize := hmarks.1
      simp_all
    · intro i hi' hmove
      rcases hi' with hi' | rfl
      · exact (hs.2.1 hs.1).2.2 i hi' hmove
      · exact ⟨hd, fun e hlo hhi => hrow e hlo (by omega)⟩
  case vc9.step.isFalse =>
    grind

private theorem image_iff (G : Hex.SparseGraph n) (p : Perm n) (raw : Array Nat)
    (hp : ∀ i : Fin n, raw[i.val]! = (p.get i).val) (i v : Fin n) :
    Image (.ofGraph G) raw i.val v.val ↔ v ∈ (G.nbrs i).toList.map p.get := by
  constructor
  · rintro ⟨e, hlo, hhi, he⟩
    have hb := G.edge_lt hhi
    rw [Graph.neighbor_ofGraph G e hb, hp] at he
    exact List.mem_map.mpr ⟨G.neighbors[e],
      Array.mem_toList_iff.mpr (G.edge_mem i hlo hhi), Fin.ext he⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨e, hlo, hhi, he⟩ := G.mem_edge (Array.mem_toList_iff.mp hw)
    have hb := G.edge_lt hhi
    rw [getElem?_pos G.neighbors e hb, Option.some.injEq] at he
    refine ⟨e, hlo, hhi, ?_⟩
    rw [Graph.neighbor_ofGraph G e hb, he, hp]

private theorem mem_iff_of_subset {α : Type} {xs ys : List α}
    (hn : xs.Nodup) (hlen : xs.length = ys.length) (hsub : xs ⊆ ys) (v : α) :
    v ∈ xs ↔ v ∈ ys := by
  classical
  refine ⟨fun hv => hsub hv, fun hv => ?_⟩
  by_cases hx : v ∈ xs
  · exact hx
  · have hle := (List.nodup_cons.mpr ⟨hx, hn⟩).length_le_of_subset
      (l₂ := ys) (fun w hw => by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hv
        · exact hsub hw)
    simp only [List.length_cons] at hle
    omega

private theorem rowOk_iff (G : Hex.SparseGraph n) (p : Perm n) (raw : Array Nat)
    (hp : ∀ i : Fin n, raw[i.val]! = (p.get i).val) (i : Fin n) :
    RowOk (.ofGraph G) raw i.val ↔
      ∀ j, G.adj (p.get i) (p.get j) = G.adj i j := by
  have hm (v : Fin n) : v ∈ (G.nbrs i).toList.map p.get ↔
      G.adj i (p.inv.get v) = true := by
    rw [List.mem_map, ← Hex.SparseGraph.mem_nbrs]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using Array.mem_toList_iff.mp hw
    · intro hv
      exact ⟨p.inv.get v, Array.mem_toList_iff.mpr hv, p.get_inv_get v⟩
  constructor
  · intro h
    have hd : G.degree (p.get i) = G.degree i := by
      simpa only [Graph.degree, Graph.ofGraph, hp, Hex.SparseGraph.degree] using h.1
    have hlen : (G.nbrs (p.get i)).toList.length =
        ((G.nbrs i).toList.map p.get).length := by
      simpa only [Hex.SparseGraph.degree_eq_size, Array.length_toList,
        List.length_map] using hd
    have hsub : (G.nbrs (p.get i)).toList ⊆ (G.nbrs i).toList.map p.get := by
      intro v hv
      obtain ⟨e, hlo, hhi, he⟩ := G.mem_edge (Array.mem_toList_iff.mp hv)
      have hb := G.edge_lt hhi
      rw [getElem?_pos G.neighbors e hb, Option.some.injEq] at he
      apply (image_iff G p raw hp i v).mp
      have hrow := h.2 e (by simpa only [Graph.ofGraph, hp] using hlo)
        (by simpa only [Graph.ofGraph, hp] using hhi)
      simpa only [Graph.neighbor_ofGraph G e hb, he] using hrow
    have he := mem_iff_of_subset (xs := (G.nbrs (p.get i)).toList)
      ((G.sorted (p.get i)).imp fun h => Fin.ne_of_lt h) hlen hsub
    intro j
    rw [Bool.eq_iff_iff, ← Hex.SparseGraph.mem_nbrs,
      ← Array.mem_toList_iff, he, hm, Perm.inv_get_get]
  · intro h
    have he (v : Fin n) : v ∈ (G.nbrs (p.get i)).toList ↔
        v ∈ (G.nbrs i).toList.map p.get := by
      rw [Array.mem_toList_iff, Hex.SparseGraph.mem_nbrs, hm,
        ← h (p.inv.get v), Perm.get_inv_get]
    have hperm : (G.nbrs (p.get i)).toList.Perm ((G.nbrs i).toList.map p.get) :=
      (List.perm_ext_iff_of_nodup
        ((G.sorted (p.get i)).imp fun h => Fin.ne_of_lt h)
        ((G.sorted i).map p.get (fun _ _ h he => Fin.ne_of_lt h (p.get_inj he)))).mpr he
    constructor
    · change G.degree ⟨raw[i.val]!, by rw [hp]; exact (p.get i).isLt⟩ = G.degree i
      have hi : (⟨raw[i.val]!, by rw [hp]; exact (p.get i).isLt⟩ : Fin n) = p.get i :=
        Fin.ext (hp i)
      rw [hi, Hex.SparseGraph.degree_eq_size, Hex.SparseGraph.degree_eq_size]
      simpa using hperm.length_eq
    · intro e hlo hhi
      have hhi' : e < G.offsets[(p.get i).val + 1]! := by
        simpa only [Graph.ofGraph, hp] using hhi
      have hb := G.edge_lt hhi'
      rw [Graph.neighbor_ofGraph G e hb]
      apply (image_iff G p raw hp i (G.neighbors[e])).mpr
      apply (he _).mp
      exact Array.mem_toList_iff.mpr (G.edge_mem (p.get i)
        (by simpa only [Graph.ofGraph, hp] using hlo) hhi')

/-- The executed sparse automorphism test accepts exactly the adjacency-
preserving permutations. Its degree checks, reused generation marks, and
fixed-vertex shortcut require no additional correctness assumptions. -/
theorem isautom_iff (G : Hex.SparseGraph n) (p : Perm n) (raw : Array Nat)
    (hp : ∀ i : Fin n, raw[i.val]! = (p.get i).val) :
    isautom (.ofGraph G) raw = true ↔
      ∀ i j, G.adj (p.get i) (p.get j) = G.adj i j := by
  rw [isautom_rows G raw (fun i hi => by rw [hp ⟨i, hi⟩]; exact (p.get ⟨i, hi⟩).isLt),
    autom_iff_moved G p]
  constructor
  · intro h i hi
    apply (rowOk_iff G p raw hp i).mp
    apply h i.val i.isLt
    rw [hp]
    exact fun he => hi (Fin.ext he)
  · intro h i hi hmove
    apply (rowOk_iff G p raw hp ⟨i, hi⟩).mpr
    apply h
    intro he
    apply hmove
    rw [hp ⟨i, hi⟩, he]

end Hex.GraphIso.Nauty.Sparse
