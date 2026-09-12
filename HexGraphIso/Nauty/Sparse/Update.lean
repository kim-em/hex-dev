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

private theorem get_set (a : Array Nat) (i v j : Nat) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  by_cases he : i = j
  · subst i
    rw [Array.getElem!_set!_self _ _ _ hj, ite_eq_left rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ he, ite_eq_right he]

private theorem extract_eq {a b : Array Nat} {lo hi : Nat}
    (hs : a.size = b.size) (he : ∀ e, lo ≤ e → e < hi → a[e]! = b[e]!) :
    a.extract lo hi = b.extract lo hi := by
  apply Array.ext
  · simp [hs]
  · intro i hi' hj'
    simp only [Array.getElem_extract]
    have h := he (lo + i) (by omega) (by simp only [Array.size_extract] at hi'; omega)
    have hb : lo + i < a.size := by simp only [Array.size_extract] at hi'; omega
    rwa [getElem!_pos a (lo + i) hb, getElem!_pos b (lo + i) (by omega)] at h

/-- Changing uninstalled entries does not change the installed rows. -/
theorem Rows.Prefix.congr {R S : Rows n} {H : Hex.SparseGraph n} {count : Nat}
    (h : R.Prefix H count) (ho : S.offsets.size = R.offsets.size)
    (hn : S.neighbors.size = R.neighbors.size)
    (he : ∀ i, i ≤ count → S.offsets[i]! = R.offsets[i]!)
    (hv : ∀ e, e < H.offsets[count]! → S.neighbors[e]! = R.neighbors[e]!) :
    S.Prefix H count := by
  refine ⟨h.count_le, ho.trans h.offsets_size, hn.trans h.neighbors_size,
    fun i hi => (he i hi).trans (h.offsets_eq i hi), ?_⟩
  intro i hi
  have hr : Hex.SparseGraph.row S.offsets S.neighbors i.val =
      Hex.SparseGraph.row R.offsets R.neighbors i.val := by
    unfold Hex.SparseGraph.row
    rw [he i.val (by omega), he (i.val + 1) (by omega)]
    apply extract_eq hn
    intro e _ hlt
    apply hv
    rw [h.offsets_eq (i.val + 1) (by omega)] at hlt
    exact Nat.lt_of_lt_of_le hlt (H.offset_mono (by omega) h.count_le)
  rw [hr]
  exact h.rows_perm i hi

private theorem extract_map (a : Array Nat) (f : Nat → Nat) (lo start len : Nat)
    (hb : lo + len ≤ a.size)
    (h : ∀ j, j < len → a[lo + j]! = f (start + j)) :
    (a.extract lo (lo + len)).toList = (List.range' start len).map f := by
  apply List.ext_getElem
  · simp only [Array.length_toList, Array.size_extract, List.length_map, List.length_range']
    omega
  · intro i hi hj
    simp only [Array.getElem_toList, Array.getElem_extract,
      List.getElem_map, List.getElem_range']
    have hil : i < len := by simpa using hj
    have he := h i hil
    rw [getElem!_pos _ _ (by omega)] at he
    simpa only [Nat.one_mul] using he

private theorem extend {R : Rows n} {H : Hex.SparseGraph n} {count : Nat}
    (h : R.Prefix H count) (hc : count < n) (a : Array Nat)
    (hs : a.size = R.neighbors.size)
    (he : ∀ e, e < H.offsets[count]! → a[e]! = R.neighbors[e]!)
    (hp : (a.extract H.offsets[count]! H.offsets[count + 1]!).toList.Perm
      ((H.nbrs ⟨count, hc⟩).toList.map Fin.val)) :
    (Rows.mk (R.offsets.set! (count + 1) H.offsets[count + 1]!) a).Prefix H (count + 1) := by
  have hos := h.offsets_size
  have hbefore : (Rows.mk (R.offsets.set! (count + 1) H.offsets[count + 1]!) a).Prefix
      H count := h.congr (by simp) hs (by
        intro i hi
        rw [get_set _ _ _ _ (by omega), ite_eq_right (by omega)]) he
  have hlast : (R.offsets.set! (count + 1) H.offsets[count + 1]!)[count + 1]! =
      H.offsets[count + 1]! := by rw [get_set _ _ _ _ (by omega), ite_eq_left rfl]
  refine ⟨by omega, hbefore.offsets_size, hbefore.neighbors_size, ?_, ?_⟩
  · intro i hi
    by_cases heq : i = count + 1
    · subst i
      exact hlast
    · exact hbefore.offsets_eq i (by omega)
  · intro i hi
    by_cases heq : i.val = count
    · have hv : i = ⟨count, hc⟩ := Fin.ext heq
      subst i
      change (a.extract _ _).toList.Perm _
      rw [hlast, hbefore.offsets_eq count (Nat.le_refl count)]
      exact hp
    · exact hbefore.rows_perm i (by omega)

private theorem copy_step (a b : Array Nat) (f : Nat → Nat) (lo start len pos e : Nat)
    (pref suff : List Nat) (hr : List.range' start len = pref ++ e :: suff)
    (hb : lo + len ≤ b.size)
    (h : a.size = b.size ∧ pos = lo + pref.length ∧
      (∀ j, j < lo → a[j]! = b[j]!) ∧
      ∀ j ∈ pref, a[lo + (j - start)]! = f j) :
    (a.set! pos (f e)).size = b.size ∧ pos + 1 = lo + (pref.length + 1) ∧
      (∀ j, j < lo → (a.set! pos (f e))[j]! = b[j]!) ∧
      ∀ j ∈ pref ++ [e], (a.set! pos (f e))[lo + (j - start)]! = f j := by
  have he := List.eq_of_range'_eq_append_cons hr
  have hl := congrArg List.length hr
  simp only [List.length_range', List.length_append, List.length_cons, Nat.one_mul] at he hl
  refine ⟨by simpa using h.1, by omega, ?_, ?_⟩
  · intro j hj
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.2.2.1 j hj
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨k, _, hp, _⟩ := List.range'_eq_append_iff.mp hr
      have hpl : pref.length = k := by simp [hp]
      have hj' : start ≤ j ∧ j < start + k := by simpa [hp] using hj
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      exact h.2.2.2 j hj
    · have hj' : j = e := by simpa using hj
      subst j
      have hp : lo + (e - start) = pos := by omega
      rw [hp, Array.getElem!_set!_self _ _ _ (by omega)]

/-- Install the remaining rows when each source row, after inverse scatter,
is a permutation of the corresponding normalized target row. -/
theorem updatecan_prefix (g : Graph n) (H : Hex.SparseGraph n) (R : Rows n)
    (lab : Array Nat) (same : Nat) (hR : R.Prefix H same)
    (hrow : ∀ i : Fin n,
      ((List.range' g.offsets[lab[i.val]!]!
        (g.offsets[lab[i.val]! + 1]! - g.offsets[lab[i.val]!]!)).map
        fun e => (inverse n lab)[g.neighbor e]!).Perm ((H.nbrs i).toList.map Fin.val)) :
    (updatecan g R lab same).Prefix H n := by
  unfold updatecan
  apply Id.of_wp_run_eq rfl (fun r : Rows n => r.Prefix H n)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      (Rows.mk (s.1.set! (same + cursor.prefix.length) s.2.2) s.2.1).Prefix
        H (same + cursor.prefix.length) ∧
      s.2.2 = H.offsets[same + cursor.prefix.length]!⌝
  | inv2 pref i suff hr s oldoffsets oldpair oldneighbors oldk offsets v hs => ⇓⟨cursor, t⟩ => ⌜
      t.1.size = s.2.1.size ∧ t.2 = s.2.2 + cursor.prefix.length ∧
      (∀ e, e < s.2.2 → t.1[e]! = s.2.1[e]!) ∧
      ∀ e ∈ cursor.prefix,
        t.1[s.2.2 + (e - g.offsets[lab[i]!]!)]! = (inverse n lab)[g.neighbor e]!⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.div_one,
      List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      List.length_range', Nat.add_zero] at *
  case vc2.step.pre => simp
  case vc1.step =>
    rename_i pref i suff s off pair ns k off' v hout pref' j suff' t ns' k' ns'' k'' hin hr he
    have hi := List.mem_of_range'_eq_append_cons hr
    have hic := List.eq_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.one_mul] at hi hic
    have hib : i < n := by omega
    have hlen := (hrow ⟨i, hib⟩).length_eq
    simp only [List.length_map, List.length_range', Array.length_toList,
      ← Hex.SparseGraph.degree_eq_size, Hex.SparseGraph.degree] at hlen
    have hmono := H.offset_mono (i := i) (j := i + 1) (by omega) (by omega)
    have hbound := H.offset_le (i := i + 1) (by omega)
    have hsize : s.2.1.size = H.neighbors.size := hout.1.neighbors_size
    apply copy_step _ _ _ _ _ _ _ _ _ _ he ?_ hin
    rw [hout.2, ← hic]
    omega
  case vc3.step.post.success =>
    rename_i pref i suff s off pair ns k off' v hout r ns' k' hr hin
    have hi := List.mem_of_range'_eq_append_cons hr
    have hic := List.eq_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.one_mul] at hi hic
    have hib : i < n := by omega
    have hlen := (hrow ⟨i, hib⟩).length_eq
    simp only [List.length_map, List.length_range', Array.length_toList,
      ← Hex.SparseGraph.degree_eq_size, Hex.SparseGraph.degree] at hlen
    have hmono := H.offset_mono (i := i) (j := i + 1) (by omega) (by omega)
    have hbound := H.offset_le (i := i + 1) (by omega)
    have hsize : s.2.1.size = H.neighbors.size := hout.1.neighbors_size
    have hk : r.2 = H.offsets[i + 1]! := by
      rw [hin.2.1, hout.2, ← hic]
      omega
    have hn : same + (pref.length + 1) = i + 1 := by omega
    rw [hn, hk]
    refine ⟨?_, rfl⟩
    apply extend (R := ⟨s.1.set! i s.2.2, s.2.1⟩) (H := H)
      (by simpa only [← hic] using hout.1) hib r.1 hin.1
    · intro e he
      apply hin.2.2.1
      rwa [hout.2, ← hic]
    · have hcopy := extract_map r.1 (fun e => (inverse n lab)[g.neighbor e]!)
        s.2.2 g.offsets[lab[i]!]! (g.offsets[lab[i]! + 1]! - g.offsets[lab[i]!]!)
        (by rw [hout.2, ← hic]; omega) (by
          intro j hj
          have he := hin.2.2.2 (g.offsets[lab[i]!]! + j) (by simp; omega)
          simpa only [Nat.add_sub_cancel_left] using he)
      have he : s.2.2 + (g.offsets[lab[i]! + 1]! - g.offsets[lab[i]!]!) =
          H.offsets[i + 1]! := by rw [← hin.2.1]; exact hk
      rw [he, hout.2, ← hic] at hcopy
      rw [hcopy]
      exact hrow ⟨i, hib⟩
  case vc4.pre =>
    have hk : (if (same == 0) = true then 0 else R.offsets[same]!) = R.offsets[same]! := by
      split
      · next hz =>
        have he : same = 0 := by simpa using hz
        subst same
        rw [hR.offsets_eq 0 (Nat.le_refl 0), H.offset_zero]
      · rfl
    rw [hk]
    have hs : same < R.offsets.size := by have := hR.count_le; have := hR.offsets_size; omega
    rw [getElem!_pos R.offsets same hs]
    simp only [Array.set!, Array.setIfInBounds, hs, dite_true, Array.set_getElem_self]
    exact ⟨hR, by simpa only [getElem!_pos R.offsets same hs] using hR.offsets_eq same (Nat.le_refl same)⟩
  case vc5.post.success =>
    rename_i hr
    have he : same + (n - same) = n := by have := hR.count_le; omega
    simpa only [he] using hr.1


/-- The executed source-row scan emits inverse-labelled neighbours. -/
theorem source_row (G : Hex.SparseGraph n) (lab : Array Nat) (l : Label n)
    (hl : Label.ofArray? n lab = some l) (i : Fin n) :
    ((List.range' G.offsets[lab[i.val]!]!
      (G.offsets[lab[i.val]! + 1]! - G.offsets[lab[i.val]!]!)).map
      fun e => (inverse n lab)[(Graph.ofGraph G).neighbor e]!) =
      (G.nbrs (l.get i)).toList.map (fun v => (l.toPerm.get v).val) := by
  have hv : lab[i.val]! = (l.get i).val := (Label.ofArray?_get hl i.val i.isLt).symm
  rw [hv]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range', Array.length_toList,
      ← Hex.SparseGraph.degree_eq_size, Hex.SparseGraph.degree]
  · intro j hj hk
    simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Array.getElem_toList]
    have hbound : G.offsets[(l.get i).val]! + j < G.offsets[(l.get i).val + 1]! := by
      have hm := G.offset_mono (i := (l.get i).val) (j := (l.get i).val + 1)
        (by omega) (by omega)
      simp only [List.length_map, List.length_range'] at hj
      omega
    rw [Graph.neighbor_ofGraph G _ (G.edge_lt hbound), inverse_toPerm hl]
    simp only [Hex.SparseGraph.nbrs, Hex.SparseGraph.row, Array.getElem_extract]

/-- The exact canonical installation represents native relabelling, even
when its retained prefix and copied rows use different neighbour orders. -/
theorem updatecan_relabel (G : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat)
    (l : Label n) (same : Nat) (hl : Label.ofArray? n lab = some l)
    (hR : R.Prefix (G.relabel l.perm) same) :
    (updatecan (.ofGraph G) R lab same).Prefix (G.relabel l.perm) n := by
  apply updatecan_prefix _ _ _ _ _ hR
  intro i
  change ((List.range' G.offsets[lab[i.val]!]!
    (G.offsets[lab[i.val]! + 1]! - G.offsets[lab[i.val]!]!)).map
    fun e => (inverse n lab)[(Graph.ofGraph G).neighbor e]!).Perm _
  rw [source_row G lab l hl i]
  simpa only [Label.get, Label.toPerm, List.map_map, Function.comp_def] using
    ((G.nbrs_relabel_perm l.perm i).symm.map Fin.val)

/-- The initial canonical allocation suffices for every checked label. -/
theorem updatecan_blank (G : Hex.SparseGraph n) (lab : Array Nat) (l : Label n)
    (hl : Label.ofArray? n lab = some l) :
    (updatecan (.ofGraph G) (Graph.ofGraph G).blank lab 0).Prefix (G.relabel l.perm) n := by
  apply updatecan_relabel G _ lab l 0 hl
  refine ⟨by omega, by simp [Graph.blank], ?_, ?_, ?_⟩
  · simp [Graph.blank, Graph.ofGraph]
  · intro i hi
    have he : i = 0 := by omega
    subst i
    rw [(G.relabel l.perm).offset_zero]
    simp [Graph.blank]
  · intro i hi
    omega

/-- Canonical installation retains the literal entries of the shared prefix,
not just its represented adjacency. -/
theorem updatecan_before (g : Graph n) (R : Rows n) (lab : Array Nat) (same : Nat)
    (hs : same ≤ n) :
    (∀ i, i < same → (updatecan g R lab same).offsets[i]! = R.offsets[i]!) ∧
      ∀ e, e < (if same = 0 then 0 else R.offsets[same]!) →
        (updatecan g R lab same).neighbors[e]! = R.neighbors[e]! := by
  unfold updatecan
  apply Id.of_wp_run_eq rfl (fun r : Rows n =>
    (∀ i, i < same → r.offsets[i]! = R.offsets[i]!) ∧
      ∀ e, e < (if same = 0 then 0 else R.offsets[same]!) → r.neighbors[e]! = R.neighbors[e]!)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜
      (∀ i, i < same → s.1[i]! = R.offsets[i]!) ∧
      (if same = 0 then 0 else R.offsets[same]!) ≤ s.2.2 ∧
      ∀ e, e < (if same = 0 then 0 else R.offsets[same]!) → s.2.1[e]! = R.neighbors[e]!⌝
  | inv2 => ⇓⟨_, s⟩ => ⌜
      (if same = 0 then 0 else R.offsets[same]!) ≤ s.2 ∧
      ∀ e, e < (if same = 0 then 0 else R.offsets[same]!) → s.1[e]! = R.neighbors[e]!⌝
  with grind [Array.getElem!_set!_ne]

end Hex.GraphIso.Nauty.Sparse
