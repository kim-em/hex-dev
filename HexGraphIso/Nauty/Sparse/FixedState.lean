/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Reach
public import HexGraphIso.Nauty.Policy.FixedState
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native refinement retains the literal position of every fixed
singleton and both of its old boundaries. -/
theorem fixed_visit {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : NodeInv G level numcells st) (hf : FixedCells level st.frame) :
    FixedCells level (visit (.ofGraph G.graph) level numcells st).2.2.frame := by
  have hr := refineWith_state G.graph level st.lab st.ptn st.active numcells st.canong.scratch
    h.spec.label h.spec.node.ptnSize (by simpa only [h.spec.node.ptnSize] using h.spec.node.ptnEnd)
    h.spec.node.starts h.scratch
  intro v hv hm
  obtain ⟨q, hq, he, hc⟩ := hf v hv hm
  refine ⟨q, hq, (cellsPerm_singleton hr.2.2.2.1 hc).trans he, ?_⟩
  obtain ⟨hpos, hstart, _, hend⟩ := hc
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases hstart with he | he
    · exact Or.inl he
    · right
      change (refineWith (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch).ptn[q - 1]! ≤ level
      rw [hr.2.2.1.closed _ he]
      exact he
  · intro i hi hj
    omega
  · change (refineWith (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch).ptn[q + 1 - 1]! ≤ level
    rw [hr.2.2.1.closed _ hend]
    exact hend

theorem compare_fixed (level code : Nat) (st : State n) :
    (compareCodes level code st).fixedpts = st.fixedpts :=
  Nauty.compare_fixed level code st

/-- Actual cached target selection leaves the individualized path unchanged. -/
theorem target_fixed (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.fixedpts = st.fixedpts := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.fixedpts = st.fixedpts)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify_fixed (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.fixedpts = st.fixedpts := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.fixedpts, ite_self]

theorem leaf_fixed (leaf : Leaf) (level : Nat) (st : State n) :
    (leafExit leaf level st).2.fixedpts = st.fixedpts :=
  Nauty.leaf_fixed leaf level st

theorem cheap_fixed (first : Bool) (level : Nat) (st : State n) :
    (cheapCheck first level st).fixedpts = st.fixedpts :=
  Nauty.cheap_fixed first level st

theorem recover_fixed (inf level : Nat) (st : State n) :
    ((policy (n := n)).recover inf level st).fixedpts = st.fixedpts :=
  Nauty.recover_fixed inf level st

theorem afterSweep_fixed (first : Bool) (level size index : Nat) (st : State n) :
    ((policy (n := n)).afterSweep first level size index st).fixedpts = st.fixedpts := by
  change (if first then { (Nauty.afterSweep first level size index st) with
    order := (Nauty.afterSweep first level size index st).order * index }
    else Nauty.afterSweep first level size index st).fixedpts = st.fixedpts
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  all_goals exact Nauty.afterSweep_fixed _ _ _ _ st

/-- Actual sparse child entry adds a fresh fixed vertex in a singleton
cell. The native cache invalidation does not affect that path fact. -/
theorem fixed_child {G : GraphIso.Sparse.Colored n k} {level numcells tc tv : Nat}
    {st : State n} {cell : VSet n} (first : Bool) (hn : 0 < n)
    (h : Ready G level numcells st) (hf : FixedCells level st.frame)
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    st.fixedpts.mem tv = false ∧
      FixedCells (level + 1) ((policy (n := n)).child first level tc tv st).frame := by
  have hc := Nauty.fixed_child first hn h.ok hf ht hv
  refine ⟨hc.1, ?_⟩
  cases first <;> exact hc.2

/-- Recovering a returned child's partition preserves all parent fixed
singletons once its temporary fixed vertex has been removed. -/
theorem fixed_recover {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st out : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (h : Ready G level numcells st)
    (hf : FixedCells level st.frame) (hx : FrameOut G level level st out)
    (he : out.fixedpts = st.fixedpts) :
    FixedCells level ((policy (n := n)).recover (n + 2) level out).frame :=
  hf.ofEffect ((recover_fixed (n + 2) level out).trans he) (h.recover hn hl hx).2.effect

/-- Removing the fresh child's fixed vertex restores the parent's bitset. -/
theorem fixed_restore {tv : Nat} {st out : State n}
    (he : out.fixedpts = st.fixedpts.insert tv) (hf : st.fixedpts.mem tv = false) :
    out.fixedpts.erase tv = st.fixedpts := by
  rw [he]
  apply VSet.ext
  intro v
  by_cases hv : tv = v
  · subst v
    simp only [VSet.mem_erase, beq_self_eq_true, Bool.not_true, Bool.and_false, hf]
  · simp only [VSet.mem_erase, VSet.mem_insert, beq_eq_false_iff_ne.mpr hv,
      Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true]

end Hex.GraphIso.Nauty.Sparse
