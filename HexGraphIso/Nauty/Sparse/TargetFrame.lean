/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.DispatchFrame
public import HexGraphIso.Nauty.Sparse.TargetValid
import all HexGraphIso.Nauty.Policy.Generic.Reach

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem target_empty (level tc : Nat) (st : State n) :
    Generic.Target State.frame level tc VSet.empty st :=
  ⟨0, fun h => (h rfl).elim, fun _ h => by simp at h⟩

/-- A fresh native target denotes exactly a bounded nontrivial partition
cell, with each selected vertex drawn from its current labels. -/
theorem fresh_target (G : Hex.SparseGraph n) (level tcLevel : Nat) (hint : Int) (st : State n)
    (hp : st.lab.toList.Perm (List.range n)) (hs : st.ptn.size = n)
    (hend : st.ptn[n - 1]! ≤ level) (hc : bcount st.ptn level n < n) :
    let t := maketargetcell (.ofGraph G) st.lab st.ptn level tcLevel hint
    Generic.Target State.frame level t.1 t.2.1 st := by
  obtain ⟨ht, hn, hb⟩ := maketargetcell_valid G st.lab st.ptn level tcLevel hint hp hs hend hc
  refine ⟨_, fun _ => ⟨ht, hn, hb⟩, ?_⟩
  intro v hv
  dsimp only [maketargetcell] at hv ⊢
  rw [mem_worksetOf] at hv
  obtain ⟨w, hw, he⟩ := List.any_eq_true.mp ((Bool.and_eq_true _ _).mp hv).2
  have he : w = v := beq_iff_eq.mp he
  subst w
  have hge : targetcell (.ofGraph G) st.lab st.ptn level tcLevel hint ≤
      cellEnd st.ptn level (targetcell (.ofGraph G) st.lab st.ptn level tcLevel hint) := cellEnd_ge
  have hlen (a b : Nat) (h : a ≤ b) : b + 1 - a = b - a + 1 := by omega
  simpa only [State.frame, hlen _ _ hge] using hw

/-- The cached target supplies the identical cell-membership contract using
the proved fresh/cached dispatch equality and a constructed parsed label. -/
theorem cached_target (G : Hex.SparseGraph n) (level tcLevel : Nat) (hint : Int) (st : State n)
    (hp : st.lab.toList.Perm (List.range n)) (hs : st.ptn.size = n)
    (hend : st.ptn[n - 1]! ≤ level) (hc : bcount st.ptn level n < n)
    (hv : Scratch.Valid n st.lab st.ptn level st.canong.scratch) :
    let t := maketargetCached (.ofGraph G) st.lab st.ptn level tcLevel hint st.canong.scratch
    Generic.Target State.frame level t.1 t.2.1 st := by
  obtain ⟨label, hl⟩ := Label.ofArray?_exists hp
  have he := maketargetCached_eq G st.lab st.ptn level tcLevel hint st.canong.scratch label hl
    hs hend hv (Target.nonempty hs hend hc)
  have ht := fresh_target G level tcLevel hint st hp hs hend hc
  have hpos := congrArg Prod.fst he
  have hset := congrArg (fun t : Nat × VSet n × Nat => t.2.1) he
  dsimp only at hpos hset ⊢
  rw [hpos, hset]
  exact ht

namespace Ready

/-- The actual target-selection guards produce either an empty target or a
nontrivial current cell. Both first and hinted off-path dispatches are covered. -/
theorem target {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) (first : Bool) (tcLevel : Nat) :
    let t := chooseTarget first (.ofGraph G.graph) tcLevel level numcells st
    Generic.Target State.frame level t.1.toNat t.2.1 t.2.2.2 := by
  have hp := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  have hend : st.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn h.ok hl
    change st.ptn[st.ptn.size - 1]! ≤ level at he
    have hs : st.ptn.size = n := h.ok.ptnSize
    rwa [hs] at he
  have choose (hint : Int) (hc : numcells < n) := cached_target G.graph level tcLevel hint st hp
    h.ok.ptnSize hend (by have := h.ok.count; exact this ▸ hc) h.scratch
  apply Generic.Target.of_out (hout := (h.target_frame first tcLevel).frame.effect)
  unfold chooseTarget
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd, ite_self]
  cases first with
  | true =>
    simp only [Bool.not_true, Bool.false_and, ite_true, Bool.false_eq_true, ite_false]
    split
    · rename_i hguard
      have hc := bne_iff_ne.mp hguard
      have hb := bcount_le st.ptn level n
      have hh := h.ok.count
      change numcells = bcount st.ptn level n at hh
      exact choose (-1) (by omega)
    · exact target_empty level _ st
  | false =>
    simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ite_false]
    split
    · rename_i hguard
      exact choose _ (of_decide_eq_true ((Bool.and_eq_true _ _).mp hguard).1)
    · exact target_empty level _ st

end Ready
end Hex.GraphIso.Nauty.Sparse
