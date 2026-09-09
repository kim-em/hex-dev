/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.PathStab
public import HexGraphIso.Nauty.Policy.Partition
public import HexGraphIso.Nauty.Policy.EquitableState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Bookkeeping on other fields preserves the fixed singleton cells. -/
theorem FixedCells.fields {level : Nat} {st out : Search n}
    (h : FixedCells level st) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.fixedpts = st.fixedpts) : FixedCells level out := by
  intro v hv hm
  rw [hf] at hm
  obtain ⟨q, hq, hlabel, hcell⟩ := h v hv hm
  exact ⟨q, hq, by rw [hl]; exact hlabel, by rw [hp]; exact hcell⟩

/-- Refinement leaves every recorded fixed vertex in a singleton cell. -/
theorem fixed_visit {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (h : FixedCells level st) :
    FixedCells level (visit ctx level numcells st).2.2 :=
  h.refine hok.labSize hok.ptnSize (searchOk_end hn0 hok hlevel)

/-- Comparison changes no fixed vertex or partition field. -/
theorem compare_fixed (level code : Nat) (st : Search n) :
    (compareCodes level code st).fixedpts = st.fixedpts := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.fixedpts, ite_self]

/-- Target selection changes no fixed vertex. -/
theorem target_fixed (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (chooseTarget first ctx tcLevel level numcells st).2.2.2.fixedpts = st.fixedpts := by
  cases first
  · rw [chooseTarget_fields]
  · rw [chooseFirst_fields]

/-- Classification fills scratch data without changing the fixed-point set. -/
theorem classify_fixed (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.fixedpts = st.fixedpts := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.fixedpts, ite_self]

private theorem admit_fixed (st : Search n) : (admit st).fixedpts = st.fixedpts := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

private theorem prune_fixed (level : Nat) (st : Search n) :
    (pruneReturn level st).2.fixedpts = st.fixedpts := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

/-- Leaf actions leave the current individualized path unchanged. -/
theorem leaf_fixed (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.fixedpts = st.fixedpts := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first | rfl | exact admit_fixed _ | exact prune_fixed level _

/-- The cheap-boundary test changes no fixed vertex. -/
theorem cheap_fixed (first : Bool) (level : Nat) (st : Search n) :
    (cheapCheck first level st).fixedpts = st.fixedpts := by
  unfold cheapCheck
  split <;> rfl

/-- Partition recovery keeps the caller's fixed-point bitset. -/
theorem recover_fixed (inf level : Nat) (st : Search n) :
    (Nauty.recover inf level st).fixedpts = st.fixedpts := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.fixedpts, ite_self]

/-- Sweep completion changes only counters. -/
theorem afterSweep_fixed (first : Bool) (level size index : Nat) (st : Search n) :
    (afterSweep first level size index st).fixedpts = st.fixedpts := by
  unfold afterSweep
  split <;> rfl

/-- An actual target vertex is fresh, and individualizing it extends the
fixed singleton cells by exactly that vertex. -/
theorem fixed_child {G : Colored n k} {level numcells tc tv : Nat}
    {st : Search n} {cell : VSet n} (first : Bool) (hn0 : 0 < n)
    (hok : SearchOk G level numcells st) (h : FixedCells level st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    st.fixedpts.mem tv = false ∧ FixedCells (level + 1) (child first level tc tv st) := by
  obtain ⟨len, hcell, hmem⟩ := htarget
  obtain ⟨hc, hlen, hrange⟩ := hcell (mem_ne_empty htv)
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hmem tv htv)
  change st.lab[tc + o]! = tv at hv
  have hinj := labInj_of_reach hok.labSize hn0 hok.reach
  have hf := h.fresh (labOk_of_reach hok.labSize hok.reach) hinj hok.labSize hc hlen hrange ho
  have hch := h.breakout hinj hok.labSize hok.ptnSize hc hlen hrange ho

  rw [hv] at hf hch
  refine ⟨hf, ?_⟩
  cases first <;> exact hch

/-- Recovering a completed child restores fixed singleton cells whenever
the parent's fixed-point bitset has been restored. -/
theorem fixed_recover {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st out : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (h : FixedCells level st)
    (hout : SearchOut G level level st out) (hf : out.fixedpts = st.fixedpts) :
    FixedCells level (Nauty.recover (n + 2) level out) := by
  have hr := (reachPolicy G ctx 0 hn0).recover level numcells st out hlevel hok hout
  apply h.ofSearchOut ((recover_fixed (n + 2) level out).trans hf) hok hr.ok hr.effect

end Hex.GraphIso.Nauty
