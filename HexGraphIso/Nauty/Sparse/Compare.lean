/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompareResult
public import HexGraphIso.Nauty.Invariant.Leaves
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace Compare

/-- A row of the canonical sparse key, with an empty default beyond its order. -/
@[expose] def row (G : Hex.SparseGraph n) (i : Nat) : List (Fin n) := (graphRows G)[i]!

@[simp] theorem row_fin (G : Hex.SparseGraph n) (i : Fin n) :
    row G i.val = (G.nbrs i).toList := by
  unfold row
  rw [getElem!_pos _ i.val (by simp [graphRows])]
  simp [graphRows]

/-- The comparison reports precisely the first differing row, or all rows
when equal; its sign is the sparse row order at that position. -/
structure Result (A B : Hex.SparseGraph n) (r : Int × Nat) : Prop where
  bound : r.2 ≤ n
  agrees : ∀ i, i < r.2 → row A i = row B i
  terminal : r.2 = n → r.1 = 0
  first : ∀ i, i < n → i = r.2 →
    r.1 = ordInt (rowCmp (row A i) (row B i)) ∧ rowCmp (row A i) (row B i) ≠ .eq

theorem stop {A B : Hex.SparseGraph n} {i : Nat} {c : Ordering}
    (hi : i < n) (hp : ∀ j, j < i → row A j = row B j)
    (hc : rowCmp (row A i) (row B i) = c) (hn : c ≠ .eq) :
    Result A B (ordInt c, i) := by
  refine ⟨by omega, hp, by simp only; omega, ?_⟩
  intro j hj he
  simpa [he, hc] using hn

theorem finish {A B : Hex.SparseGraph n} (hp : ∀ j, j < n → row A j = row B j) :
    Result A B (0, n) :=
  ⟨by omega, hp, fun _ => rfl, fun _ hi he => False.elim (by omega)⟩

end Compare

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 1600000

private theorem cursor {lo hi i : Nat} {pref suff : List Nat}
    (h : List.range' lo (hi - lo) = pref ++ i :: suff) :
    lo ≤ i ∧ i < hi ∧ i = lo + pref.length := by
  have hm := List.mem_of_range'_eq_append_cons h
  have he := List.eq_of_range'_eq_append_cons h
  simp only [List.mem_range'_1] at *
  omega

/-- The executed sparse comparison identifies the first unequal canonical row. -/
theorem testcanlab_result (G H : Hex.SparseGraph n) (R : Rows n) (lab : Array Nat)
    (l : Label n) (hl : Label.ofArray? n lab = some l) (hR : R.Prefix H n) :
    Compare.Result (G.relabel l.perm) H (testcanlab (.ofGraph G) R lab) := by
  let A := G.relabel l.perm
  let read := fun e => (inverse n lab)[(Graph.ofGraph G).neighbor e]!
  have old (i : Nat) (hi : i < n) :
      RowRep (fun e => R.neighbors[e]!) R.offsets[i]! R.offsets[i + 1]!
        (Compare.row H i) := by
    rw [Compare.row_fin H ⟨i, hi⟩]
    exact RowRep.stored hR ⟨i, hi⟩
  have candidate (i : Nat) (hi : i < n) :
      RowRep read G.offsets[lab[i]!]! G.offsets[lab[i]! + 1]! (Compare.row A i) := by
    rw [Compare.row_fin A ⟨i, hi⟩]
    exact RowRep.candidate G hl ⟨i, hi⟩
  have sortedA (i : Nat) (hi : i < n) : (Compare.row A i).Pairwise (· < ·) := by
    rw [Compare.row_fin A ⟨i, hi⟩]
    exact A.sorted ⟨i, hi⟩
  have sortedH (i : Nat) (hi : i < n) : (Compare.row H i).Pairwise (· < ·) := by
    rw [Compare.row_fin H ⟨i, hi⟩]
    exact H.sorted ⟨i, hi⟩
  have unseen (i : Nat) (hi : i < n) (pref : List Nat) (e : Nat) (suff : List Nat)
      (hr : List.range' G.offsets[lab[i]!]!
        (G.offsets[lab[i]! + 1]! - G.offsets[lab[i]!]!) = pref ++ e :: suff) :
      read e ∉ pref.map read := by
    intro hm
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
    have hje := List.gt_of_range'_eq_append_cons hr (by omega) hj
    have hjr : j ∈ List.range' G.offsets[lab[i]!]!
        (G.offsets[lab[i]! + 1]! - G.offsets[lab[i]!]!) := by rw [hr]; simp [hj]
    simp only [List.mem_range'_1] at hjr
    have hc := cursor hr
    have eq := (candidate i hi).injective (sortedA i hi) hjr.1 (by omega)
      hc.1 hc.2.1 he
    omega
  unfold testcanlab
  apply Id.of_wp_run_eq rfl (fun r : Int × Nat => Compare.Result A H r)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, s⟩ => ⌜
      (s.1 = none ∨ cursor.suffix = []) ∧
      (s.1 = none → s.2.size = n ∧
        (∀ v, v < n → s.2[v]! ≤ cursor.prefix.length) ∧
        ∀ j, j < cursor.prefix.length → Compare.row A j = Compare.row H j) ∧
      (∀ r, s.1 = some r → Compare.Result A H r)⌝
  | inv2 pref i suff he s marks v di dli hdegree stamp hs =>
      ⇓⟨cursor, marks⟩ => ⌜Marks n (i + 1) marks
        (fun v => v ∈ cursor.prefix.map (fun e => R.neighbors[e]!))⌝
  | inv3 pref i suff he s marks v di dli hdegree stamp hs rowmarks hm =>
      ⇓⟨cursor, s⟩ => ⌜Diff n (i + 1) ((Compare.row H i).map Fin.val)
        (cursor.prefix.map read) s.1 s.2⌝
  | inv4 pref i suff he s marks v di dli hdegree stamp hs rowmarks hm st marks' mina hd hne =>
      ⇓⟨cursor, r⟩ => ⌜
        (r.1 = none ∨ cursor.suffix = []) ∧
        (r.1 = none → ∀ e ∈ cursor.prefix, marks'[R.neighbors[e]!]! = i + 1 → mina ≤ R.neighbors[e]!) ∧
        (∀ result, r.1 = some result → result = (-1, i) ∧
          rowCmp (Compare.row A i) (Compare.row H i) = .lt)⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, bne_iff_ne] at *
  all_goals simp_all
  case vc1.step.isTrue =>
    rename_i pref i suff st marks v di dli hout hr hne
    have hi := cursor (lo := 0) (hi := n) hr
    have hpre := (hout.2.1 hout.1).2.2
    have ho := (old i hi.2.1).length
    have ha := (candidate i hi.2.1).length
    change (Compare.row H i).length = R.degree i at ho
    change (Compare.row A i).length = (Graph.ofGraph G).degree lab[i]! at ha
    split
    · next hlt =>
      exact Compare.stop (A := A) (B := H) (i := i) (c := .lt) hi.2.1
        (by simpa [hi.2.2] using hpre)
        (RowOrder.degree_lt (by rw [ho, ha]; exact hlt)) (by decide)
    · next hlt =>
      exact Compare.stop (A := A) (B := H) (i := i) (c := .gt) hi.2.1
        (by simpa [hi.2.2] using hpre)
        (RowOrder.degree_gt (by rw [ha, ho]; omega)) (by decide)
  case vc2.step =>
    rename_i hout hm hr hdeg he
    have hi := cursor (lo := 0) (hi := n) hr
    have hc := cursor he
    exact hm.set ((old _ hi.2.1).bound hc.1 hc.2.1)
  case vc3.step.isFalse.pre =>
    rename_i hout hr hdeg
    have hi := cursor (lo := 0) (hi := n) hr
    have hs := hout.2.1 hout.1
    apply Marks.fresh hs.1
    intro v hv
    have := hs.2.1 v hv
    omega
  case vc4.step.isTrue =>
    rename_i hout hmark hd hr hdeg hm he
    have hi := cursor (lo := 0) (hi := n) hr
    have hc := cursor he
    exact hd.hit (by omega) ((candidate _ hi.2.1).bound hc.1 hc.2.1) hmark
  case vc5.step.isFalse.isTrue =>
    rename_i hout hmark hlt hd hr hdeg hm he
    have hi := cursor (lo := 0) (hi := n) hr
    have hc := cursor he
    have h := hd.miss ((candidate _ hi.2.1).bound hc.1 hc.2.1)
      (by simpa using unseen _ hi.2.1 _ _ _ he) hmark
    simpa only [Nat.min_eq_right (Nat.le_of_lt hlt)] using h
  case vc6.step.isFalse.isFalse =>
    rename_i hout hmark hlt hd hr hdeg hm he
    have hi := cursor (lo := 0) (hi := n) hr
    have hc := cursor he
    have h := hd.miss ((candidate _ hi.2.1).bound hc.1 hc.2.1)
      (by simpa using unseen _ hi.2.1 _ _ _ he) hmark
    simpa only [Nat.min_eq_left hlt] using h
  case vc7.step.isFalse.post.success.pre =>
    rename_i hout hr hdeg hm
    have hi := cursor (lo := 0) (hi := n) hr
    apply Diff.initial
    apply hm.congr
    intro v hv
    simpa only [Nat.add_sub_cancel' (old _ hi.2.1).le, and_assoc] using
      (old _ hi.2.1).mem_iff v
  case vc8.step.isTrue =>
    rename_i hout hhit hin hr hdeg hm hne hd he
    have hi := cursor (lo := 0) (hi := n) hr
    have hc := cursor he
    have hd' := hd.congr_seen (fun v => (candidate _ hi.2.1).perm.mem_iff (a := v))
    exact hd'.smaller (sortedA _ hi.2.1) (sortedH _ hi.2.1)
      (by rw [(candidate _ hi.2.1).length, (old _ hi.2.1).length]; exact hdeg.symm)
      (v := ⟨_, (old _ hi.2.1).bound hc.1 hc.2.1⟩) hhit.1 hhit.2
  case vc9.step.isFalse =>
    rename_i hout hhit hin hr hdeg hm hne hd he
    intro e he hmark
    rcases he with he | rfl
    · exact hin.2.1 hin.1 e he hmark
    · exact hhit hmark
  case vc11.step.isFalse.post.success.post.success.isTrue.post.success.h_1 =>
    rename_i hout hx hr hdeg hm hne hd hresult
    have hi := cursor (lo := 0) (hi := n) hr
    exact Compare.stop (c := .lt) hi.2.1
      (by simpa [hi.2.2] using (hout.2.1 hout.1).2.2) hresult.2 (by decide)
  case vc12.step.isFalse.post.success.post.success.isTrue.post.success.h_2 =>
    rename_i hout hx hr hdeg hm hne hd hscan
    have hi := cursor (lo := 0) (hi := n) hr
    have hd' := hd.congr_seen (fun v => (candidate _ hi.2.1).perm.mem_iff (a := v))
    apply Compare.stop (c := .gt) hi.2.1
      (by simpa [hi.2.2] using (hout.2.1 hout.1).2.2) _ (by decide)
    apply hd'.greater (sortedA _ hi.2.1) (sortedH _ hi.2.1)
      (by rw [(candidate _ hi.2.1).length, (old _ hi.2.1).length]; exact hdeg.symm)
      (by have := hd'.min_le; omega)
    intro v hv hmark
    obtain ⟨e, hlo, hhi, rfl⟩ := (old _ hi.2.1).mem_iff v |>.mpr hv
    exact hscan e hlo (by have := (old _ hi.2.1).le; omega) hmark
  case vc13.step.isFalse.post.success.post.success.isFalse =>
    rename_i pref i suff outer marks v di dli stamp oldmarks state marked mina hout hr hdeg hm hlast hd
    have hi := cursor (lo := 0) (hi := n) hr
    have hd' := hd.congr_seen (fun v => (candidate i hi.2.1).perm.mem_iff (a := v))
    have heq := hd'.equal (sortedA i hi.2.1) (sortedH i hi.2.1)
      (by rw [(candidate i hi.2.1).length, (old i hi.2.1).length]; exact hdeg.symm) rfl
    refine ⟨hd.marks.size, ?_, ?_⟩
    · intro v hv
      have := hd.marks.bound v hv
      omega
    · intro j hj
      by_cases hj' : j < pref.length
      · exact (hout.2.1 hout.1).2.2 j hj'
      · have he : j = i := by omega
        simpa [he] using heq
  case vc16.post.success.h_2 =>
    rename_i hx hin
    exact Compare.finish hin.2.2

end Hex.GraphIso.Nauty.Sparse
