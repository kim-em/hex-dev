/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetPrepare
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 1600000

private theorem head_range {first len : Nat} (h : 0 < len) :
    (List.range' first len).headD 0 = first := by
  cases len with
  | zero => omega
  | succ len => simp [List.range'_succ]

/-- The fresh selector's compact indices compute the same native score fold
as the cached selector, including the first maximum tie rule. -/
theorem bestcell_spec (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend) :
    bestcell (.ofGraph G) lab ptn level =
      Target.best (Target.nontrivial (cells ptn level n))
        (Target.score (.ofGraph G) lab s (Target.nontrivial (cells ptn level n))) n := by
  let keys := Target.nontrivial (cells ptn level n)
  let ranks := List.range keys.length
  let read := fun e => Target.encode keys n s.cellstart[(Graph.ofGraph G).neighbor e]!
  have hbound : ∀ i, i < n → lab[i]! < n := by
    intro i hi
    rw [← Label.ofArray?_get hl i hi]
    exact (l.get ⟨i, hi⟩).isLt
  have hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j := by
    intro i j hi hj hij
    have he : l.get ⟨i, hi⟩ = l.get ⟨j, hj⟩ := Fin.ext (by simpa only [Label.ofArray?_get hl] using hij)
    exact congrArg Fin.val (l.perm.get_inj he)
  have key_bound : ∀ k ∈ keys, k < n := fun _ hk => Target.bound hptn hend hk
  have key_length : keys.length ≤ n := Target.length_le hptn hend
  have sentinel : n ∉ keys := fun h => Nat.lt_irrefl n (key_bound n h)
  have rank_nodup : ranks.Nodup := List.nodup_range
  have rank_sentinel : n ∉ ranks := by simp only [ranks, List.mem_range]; omega
  have read_entry (first e : Nat) (hf : first < n) (he : e < G.offsets[lab[first]! + 1]!) :
      read e = n ∨ read e ∈ ranks := by
    have hv := Graph.neighbor_lt G ⟨lab[first]!, hbound first hf⟩ he
    rcases Target.vertex_index hidx hptn hend l hl ⟨_, hv⟩ with hc | hc
    · left; simp [read, hc, Target.encode]
    · right
      have hn : s.cellstart[(Graph.ofGraph G).neighbor e]! ≠ n := by
        intro heq; rw [heq] at hc; exact sentinel hc
      simp only [read, Target.encode, ite_eq_right hn, ranks, List.mem_range]
      exact List.idxOf_lt_length_of_mem hc
  have cell (first : Nat) (hf : first < n) (hb : first = 0 ∨ ptn[first - 1]! ≤ level) :=
    isCell_cellEnd (ptn := ptn) (level := level) (a := first)
      (by omega) hb (by simpa [hptn] using hend)
  have end_lt (first : Nat) (hf : first < n) : cellEnd ptn level first < n := by
    simpa [hptn] using cellEnd_lt (ptn := ptn) (level := level) (i := first)
      (by omega) (by simpa [hptn] using hend)
  have observe {starts raw : Array Nat} {first i e : Nat}
      (hscan : Target.Scan n ptn level n first starts.toList)
      (hmap : Target.MapPrefix n lab s.cellstart keys first raw)
      (hi : i < starts.size) (he : e < G.offsets[lab[starts[i]!]! + 1]!) :
      raw[(Graph.ofGraph G).neighbor e]! = read e ∧ (read e = n ∨ read e ∈ ranks) := by
    have hk := hscan.finish (Or.inl rfl)
    have hm : starts[i]! ∈ keys := by
      change starts.toList = keys at hk
      rw [← hk, ← Array.getElem!_toList, getElem!_pos _ i (by simpa using hi)]
      exact List.getElem_mem (by simpa using hi)
    have hf := key_bound _ hm
    have hv := Graph.neighbor_lt G ⟨lab[starts[i]!]!, hbound _ hf⟩ he
    exact ⟨(hmap.finish hscan.used_le).complete l hl ⟨_, hv⟩, read_entry _ _ hf he⟩
  have sized {starts sizes : Array Nat} {first i : Nat}
      (hscan : Target.Scan n ptn level n first starts.toList)
      (hsizes : sizes.toList = starts.toList.map (fun k => s.cellend[k]! - k + 1))
      (hi : i < keys.length) : sizes[i]! = s.cellend[keys[i]!]! - keys[i]! + 1 := by
    apply Target.sizes_get (keys := keys) (degree := fun k => s.cellend[k]! - k + 1)
    · simpa only [hscan.finish (Or.inl rfl)] using hsizes
    · exact hi
  have observed_score {starts : Array Nat} {first i : Nat}
      (hscan : Target.Scan n ptn level n first starts.toList) (hi : i < starts.size) :
      ranks.countP (Join.qualifies
        ((List.range' G.offsets[lab[starts[i]!]!]!
          (G.offsets[lab[starts[i]!]! + 1]! - G.offsets[lab[starts[i]!]!]!)).map read)
        (fun k => s.cellend[keys[k]!]! - keys[k]! + 1)) =
          Target.score (.ofGraph G) lab s keys keys[i]! := by
    have hk := hscan.finish (Or.inl rfl)
    change starts.toList = keys at hk
    have hm : starts[i]! ∈ keys := by
      rw [← hk, ← Array.getElem!_toList, getElem!_pos _ i (by simpa using hi)]
      exact List.getElem_mem (by simpa using hi)
    have hg : starts[i]! = keys[i]! := by rw [← hk, Array.getElem!_toList]
    have he := Target.encoded_score G lab ptn level s hidx hptn hend l hl _ (key_bound _ hm)
    simpa only [Target.row, List.map_map, Function.comp_def, hg, read, ranks, keys, Graph.ofGraph] using he
  unfold bestcell
  apply Id.of_wp_run_eq rfl (fun r : Nat => r = Target.best keys (Target.score (.ofGraph G) lab s keys) n)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, state⟩ => ⌜
      Target.Scan n ptn level cursor.prefix.length state.2.2.2 state.1.toList ∧
      Target.MapPrefix n lab s.cellstart keys state.2.2.2 state.2.2.1 ∧
      state.2.1.toList = state.1.toList.map (fun k => s.cellend[k]! - k + 1)⌝
  | inv2 => ⇓⟨cursor, raw⟩ => ⌜
      Target.MapPrefix n lab s.cellstart keys
        ((cursor.prefix ++ cursor.suffix).headD 0 + cursor.prefix.length) raw⌝
  | inv3 => ⇓⟨cursor, state⟩ => ⌜
      state.1.size = keys.length ∧ (∀ k ∈ ranks, state.1[k]! = 0) ∧
      state.2.1 < keys.length ∧
      state.2 = cursor.prefix.foldl
        (Target.select (fun i => Target.score (.ofGraph G) lab s keys keys[i]!)) (0, 0)⌝
  | inv4 => ⇓⟨cursor, hits⟩ => ⌜
      hits.size = keys.length ∧ Join.Counts ranks (cursor.prefix.map read) hits⌝
  | inv5 => ⇓⟨cursor, state⟩ => ⌜
      state.1.size = keys.length ∧ Join.Sweep ranks ((cursor.prefix ++ cursor.suffix).map read)
        (cursor.prefix.map read) (fun i => s.cellend[keys[i]!]! - keys[i]! + 1) state.1 state.2⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil, List.length_range',
      List.map_append, List.map_cons, List.map_nil, Array.toList_push, Array.size_set!,
      Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, List.append_nil, List.nil_append] at *
  case vc1.step.isTrue =>
    rename_i hg hin hr
    have hf : _ = n := Nat.le_antisymm hin.1.first_le hg
    refine ⟨⟨by omega, hin.1.first_le, hin.1.boundary, hin.1.before, ?_⟩, hin.2⟩
    exact ⟨cells ptn level n, by simp [cells.go], hin.1.finish (Or.inr hf)⟩
  case vc2.step =>
    rename_i pre it suff b os pair oz pair2 raw first hg last jp ht index ns nz hout pree j sufe out nr hin houter hr
    have hf : b.2.2.2 < n := by omega
    have hb := end_lt b.2.2.2 hf
    have hc := cell b.2.2.2 hf hout.1.boundary
    have hj := List.mem_of_range'_eq_append_cons hr
    have he := List.eq_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.one_mul] at hj he
    have hh : (pree ++ j :: sufe).headD 0 = b.2.2.2 := by rw [← hr, head_range (by omega)]
    simp only [List.append_assoc, List.singleton_append, hh] at hin ⊢
    rw [← he] at hin
    rw [show b.2.2.2 + (pree.length + (0 + 1)) = j + 1 by omega]
    apply hin.set (by omega) hbound hinj
    rw [hidx.starts_eq _ _ hc (by omega) hf j hj.1 (by omega), ite_eq_right (by omega),
      Target.encode, ite_eq_right (by omega)]
    have h_rank := hout.1.rank (by have := hout.1.used_le; omega) hf ht
    simpa only [Array.length_toList] using h_rank.symm
  case vc3.step.isFalse.isTrue.pre =>
    rename_i hout hr
    rw [head_range (by omega), Nat.add_zero]
    exact hout.2.1
  case vc4.step.isFalse.isTrue.post.success =>
    rename_i pre it suff b os pair oz pair2 raw first hg last jp ht index ns nz hout out nf hr hin
    have hf : b.2.2.2 < n := by omega
    have hs := hout.1.step hptn hend (by have := hout.1.used_le; omega) hf
    rw [ite_eq_left ht] at hs
    refine ⟨hs, ?_, ?_⟩
    · rw [head_range (by omega)] at hin
      have he : b.2.2.2 + (cellEnd ptn level b.2.2.2 + 1 - b.2.2.2) =
          cellEnd ptn level b.2.2.2 + 1 := by omega
      simpa only [he] using hin
    · rw [hout.2.2, hidx.end_eq hptn hend hf hout.1.boundary]
  case vc5.step.isFalse.isFalse =>
    rename_i pre it suff b os pair oz pair2 raw first hg last jp ht nf hin hr
    have hf : b.2.2.2 < n := by omega
    have hg : b.2.2.2 ≤ cellEnd ptn level b.2.2.2 := cellEnd_ge
    have he : cellEnd ptn level b.2.2.2 = b.2.2.2 := by omega
    have hs := hin.1.step hptn hend (by have := hin.1.used_le; omega) hf
    rw [ite_eq_right ht] at hs
    refine ⟨hs, ?_, hin.2.2⟩
    rw [he]
    apply hin.2.1.singleton
    have hc := cell b.2.2.2 hf hin.1.boundary
    have hv := hidx.starts_eq _ _ hc (by omega) hf _ (Nat.le_refl _) (by omega)
    simpa only [he, Nat.add_sub_cancel_left, ite_true] using hv
  case vc6.pre => exact ⟨.initial n ptn level, .initial _ hbound, trivial⟩
  case vc7.post.success.isTrue =>
    rename_i hempty hin
    have hk := hin.1.finish (Or.inl rfl)
    have hz : Target.nontrivial (cells ptn level n) = [] := by
      rw [← hk]
      simpa using congrArg Array.toList (Array.isEmpty_iff.mp hempty)
    simp [Target.best, hz]
  case vc8.step.isTrue =>
    rename_i pre i suff old oh pair best max v hout pree e sufe arr k nh hin hprep houter hr hne
    have hi := List.mem_of_range'_eq_append_cons houter
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at hi he
    have hx := observe (i := i) (e := e) hprep.1 hprep.2.1 (by omega) (by omega)
    rw [hx.1] at hne ⊢
    exact ⟨hin.1, hin.2.add (hx.2.resolve_left hne)⟩
  case vc9.step.isFalse =>
    rename_i pre i suff old oh pair best max v hout pree e sufe arr k hin hprep houter hr hne
    have hi := List.mem_of_range'_eq_append_cons houter
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at hi he
    have hx := observe (i := i) (e := e) hprep.1 hprep.2.1 (by omega) (by omega)
    rw [hx.1] at hne
    have hz := Decidable.of_not_not hne
    exact ⟨hin.1, hin.2.skip (by simpa only [hz] using rank_sentinel)⟩
  case vc10.step.pre =>
    rename_i hout hprep hr
    exact ⟨hout.1, Join.Counts.initial (by intro k hk; rw [hout.1]; exact List.mem_range.mp hk)
      hout.2.1⟩
  case vc11.step.isTrue.isTrue =>
    rename_i pre i suff old oh pair best max v hout counted pree e sufe arr hits count k jp nc nh hprep houter hc hr hne htest hin
    have hi := List.mem_of_range'_eq_append_cons houter
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at hi he
    have hx := observe (i := i) (e := e) hprep.1 hprep.2.1 (by omega) (by omega)
    rw [hx.1] at hne htest ⊢
    have hk := hx.2.resolve_left hne
    rw [sized hprep.1 hprep.2.2 (List.mem_range.mp hk)] at htest
    have hh := hin.2.clear rank_nodup hk (by simp)
    exact ⟨hin.1, by simpa only [htest, and_self, ite_true, List.append_assoc,
      List.singleton_append] using hh⟩
  case vc12.step.isTrue.isFalse =>
    rename_i pre i suff old oh pair best max v hout counted pree e sufe arr hits count k jp nh hprep houter hc hr hne htest hin
    have hi := List.mem_of_range'_eq_append_cons houter
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at hi he
    have hx := observe (i := i) (e := e) hprep.1 hprep.2.1 (by omega) (by omega)
    rw [hx.1] at hne htest ⊢
    have hk := hx.2.resolve_left hne
    rw [sized hprep.1 hprep.2.2 (List.mem_range.mp hk)] at htest
    have hh := hin.2.clear rank_nodup hk (by simp)
    exact ⟨hin.1, by simpa only [htest, ite_false, Nat.add_zero, List.append_assoc,
      List.singleton_append] using hh⟩
  case vc13.step.isFalse =>
    rename_i pre i suff old oh pair best max v hout counted pree e sufe arr hits count k hprep houter hc hr hne hin
    have hi := List.mem_of_range'_eq_append_cons houter
    have he := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Graph.ofGraph] at hi he
    have hx := observe (i := i) (e := e) hprep.1 hprep.2.1 (by omega) (by omega)
    rw [hx.1] at hne
    have hz := Decidable.of_not_not hne
    have hh := hin.2.skip (k := read e) (by simpa only [read, keys, hz] using rank_sentinel)
    exact ⟨hin.1, by simpa only [List.append_assoc, List.singleton_append] using hh⟩
  case vc14.step.post.success.pre =>
    rename_i hprep hr hin
    exact ⟨hin.1, Join.Sweep.initial _ hin.2⟩
  case vc15.step.post.success.post.success.isTrue =>
    rename_i pre i suff old oh pair best max v hout counted result hits count htest hprep hr hc hin
    have hi := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1] at hi
    have hk := hprep.1.finish (Or.inl rfl)
    have hsz := congrArg List.length hk
    simp only [Array.length_toList] at hsz
    obtain ⟨hcount, hz⟩ := hin.2.finish
    have hscore := hcount.trans (observed_score hprep.1 (by omega))
    refine ⟨hin.1, hz, by omega, ?_⟩
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hout.2.2.2]
    simp only [Target.select, ← hscore, ite_eq_left htest]
  case vc16.step.post.success.post.success.isFalse =>
    rename_i pre i suff old oh pair best max v hout counted result hits count htest hprep hr hc hin
    have hi := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1] at hi
    obtain ⟨hcount, hz⟩ := hin.2.finish
    have hscore := hcount.trans (observed_score hprep.1 (by omega))
    refine ⟨hin.1, hz, hout.2.2.1, ?_⟩
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hout.2.2.2]
    simp only [Target.select, ← hscore, ite_eq_right htest]
  case vc17.post.success.isFalse.pre =>
    rename_i hempty hits hin
    have hk := hin.1.finish (Or.inl rfl)
    have hs := congrArg List.length hk
    simp only [Array.length_toList] at hs
    have hp : 0 < (Target.nontrivial (cells ptn level n)).length := by
      simp only [Array.isEmpty_iff_size_eq_zero] at hempty
      omega
    refine ⟨by simpa using hs, ?_, hp, rfl⟩
    intro k hk
    simp [hs, List.mem_range.mp hk]
  case vc18.post.success.isFalse.post.success =>
    rename_i hempty initialHits result pair best hprep hin
    have hk := hprep.1.finish (Or.inl rfl)
    have hs := congrArg List.length hk
    simp only [Array.length_toList] at hs
    have hp : 0 < (Target.nontrivial (cells ptn level n)).length := by
      have := hin.2.2.1
      omega
    have hn : (Target.nontrivial (cells ptn level n)).isEmpty ≠ true := by
      intro h
      have he := List.isEmpty_iff.mp h
      rw [he] at hp
      simp at hp
    have hh (xs : List Nat) : xs[0]! = xs.headD 0 := by cases xs <;> rfl
    have hf := Target.fold_map (fun i => (Target.nontrivial (cells ptn level n))[i]!)
      (fun i => Target.score (.ofGraph G) lab s (Target.nontrivial (cells ptn level n))
        (Target.nontrivial (cells ptn level n))[i]!)
      (Target.score (.ofGraph G) lab s (Target.nontrivial (cells ptn level n)))
      (List.range (Target.nontrivial (cells ptn level n)).length) (0, 0) (fun _ _ => rfl)
    have hi := congrArg Prod.fst hf
    simp only [Target.range_get, Prod.map, id_eq, hh] at hi
    have he := hin.2.2.2
    rw [hs, ← List.range_eq_range'] at he
    rw [← he] at hi
    simpa only [Target.best, ite_eq_right hn, ← Array.getElem!_toList, hk] using hi

end Hex.GraphIso.Nauty.Sparse
