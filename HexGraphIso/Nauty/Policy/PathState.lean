/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Fixed
public import HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Pairs
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The individualized path consists of singleton cells and transports
root-stabilizing automorphisms to the current partition. -/
abbrev PathInv (G : Colored n k) (ctx : Ctx n) (level : Nat) (st : Search n) : Prop :=
  PathOk ctx (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st

/-- Bookkeeping that preserves the partition and fixed vertices preserves the path. -/
theorem PathInv.fields {G : Colored n k} {ctx : Ctx n} {level : Nat} {st out : Search n}
    (h : PathInv G ctx level st) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.fixedpts = st.fixedpts) : PathInv G ctx level out := by
  refine ⟨h.fixed.fields hl hp hf, ?_⟩
  intro γ hc hr hfix
  change CellStab out.ptn level out.lab γ
  rw [hl, hp]
  apply h.stab γ hc hr
  intro u hu hm
  apply hfix u hu
  change out.fixedpts.mem u = true
  rw [hf]
  exact hm

/-- Refinement transports the path when its active positions are cell starts. -/
theorem PathInv.visit {G : Colored n k} {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (h : PathInv G ctx level st) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = n) (hok : SearchOk G level numcells st)
    (hstarts : ∀ v, st.active.mem v = true → v = 0 ∨ st.ptn[v - 1]! ≤ level) :
    PathInv G ctx level (visit ctx level numcells st).2.2 := by
  have hr := h.refine hn0 hlevel hgsz hok hstarts
  exact ⟨hr.fixed, hr.stab⟩

/-- Code comparison preserves the current path. -/
theorem PathInv.compare {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : PathInv G ctx level st) (code : Nat) : PathInv G ctx level (compareCodes level code st) :=
  h.fields (compareCodes_frame level code st).1 (compareCodes_frame level code st).2.1
    (compare_fixed level code st)

/-- Target selection changes neither the path nor the partition. -/
theorem PathInv.target {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : PathInv G ctx level st) (first : Bool) (tcLevel numcells : Nat) :
    PathInv G ctx level (chooseTarget first ctx tcLevel level numcells st).2.2.2 :=
  h.fields (chooseTarget_frame first ctx tcLevel level numcells st).1
    (chooseTarget_frame first ctx tcLevel level numcells st).2.1
    (target_fixed first ctx tcLevel level numcells st)

/-- Classification leaves the individualized path unchanged. -/
theorem PathInv.classify {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : PathInv G ctx level st) (numcells : Nat) :
    PathInv G ctx level (classify ctx level numcells st).2 :=
  h.fields (classify_frame ctx level numcells st).1 (classify_frame ctx level numcells st).2.1
    (classify_fixed ctx level numcells st)

/-- Admissions and incumbent installation preserve the current path. -/
theorem PathInv.leaf {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : PathInv G ctx level st) (leaf : Leaf) : PathInv G ctx level (leafExit leaf level st).2 :=
  h.fields (leafExit_frame leaf level st).1 (leafExit_frame leaf level st).2.1 (leaf_fixed leaf level st)

/-- The cheap guard changes only its recorded boundary. -/
theorem PathInv.cheap {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : PathInv G ctx level st) (first : Bool) : PathInv G ctx level (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.fields rfl rfl rfl

/-- Individualizing a target vertex extends the partition-stabilization
condition to automorphisms fixing that vertex. -/
theorem PathInv.child {G : Colored n k} {ctx : Ctx n} {level numcells tc tv : Nat}
    {st : Search n} {cell : VSet n} (h : PathInv G ctx level st) (first : Bool)
    (hn0 : 0 < n) (hlevel : 1 ≤ level) (hok : SearchOk G level numcells st)
    (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    PathInv G ctx (level + 1) (child first level tc tv st) := by
  have hfixed := (fixed_child first hn0 hok h.fixed htarget htv).2
  obtain ⟨len, hcell, hmem⟩ := htarget
  obtain ⟨hc, hlen, hrange⟩ := hcell (mem_ne_empty htv)
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hmem tv htv)
  change st.lab[tc + o]! = tv at hv
  have hb : level ≤ n := Nat.le_trans hok.bc (bcount_le _ _ _)
  have hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1 := by
    intro q he
    by_cases hq : q < n
    · have hvq := hok.vals q hq
      change st.ptn[q]! ≤ level ∨ st.ptn[q]! = n + 2 at hvq
      rcases hvq with hlo | hi <;> omega
    · have hsz : st.ptn.size ≤ q := by have := hok.ptnSize; change st.ptn.size = n at this; omega
      rw [getElem!_neg st.ptn q (by omega : ¬ q < st.ptn.size)] at he
      change 0 = level + 1 at he
      omega
  have hs := h.stab.breakout hc (by rw [hok.ptnSize]; exact hrange)
    (hok.labSize.trans hok.ptnSize.symm) (labOk_of_reach hok.labSize hok.reach) ho hlen
    (searchOk_end hn0 hok hlevel) hvals

  rw [hv] at hs
  refine ⟨hfixed, ?_⟩
  cases first <;> exact hs

/-- A child's singleton active set names a cell start in its new partition. -/
theorem child_starts {level tc tv : Nat} {st : Search n} {cell : VSet n}
    (first : Bool) (htarget : Generic.Target (fun st => st) level tc cell st) (htv : cell.mem tv = true) :
    let out := child first level tc tv st
    ∀ v, out.active.mem v = true → v = 0 ∨ out.ptn[v - 1]! ≤ level + 1 := by
  intro out v hv
  obtain ⟨len, hcell, _⟩ := htarget
  have hc := (hcell (mem_ne_empty htv)).1
  have ha : out.active = VSet.empty.insert tc := by cases first <;> rfl
  have hp : out.ptn = st.ptn.set! tc (level + 1) := by cases first <;> rfl
  rw [ha, VSet.mem_insert, VSet.mem_empty, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hv
  obtain ⟨rfl, _⟩ := hv
  by_cases ht : tc = 0
  · exact Or.inl ht
  · right
    rw [hp, Array.getElem!_set!_ne _ _ _ _ (by omega)]
    have hs := hc.2.1.resolve_left ht
    change st.ptn[tc - 1]! ≤ level at hs
    omega

/-- A recovered parent keeps its path once cleanup restores its fixed set. -/
theorem PathInv.recover {G : Colored n k} {ctx : Ctx n} {level numcells : Nat} {st out : Search n}
    (h : PathInv G ctx level st) (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st) (hout : SearchOut G level level st out)
    (hf : out.fixedpts = st.fixedpts) :
    PathInv G ctx level (Nauty.recover (n + 2) level out) := by
  have hr := (reachPolicy G ctx 0 hn0).recover level numcells st out hlevel hok hout
  exact h.ofSearchOut hn0 hlevel ((recover_fixed (n + 2) level out).trans hf) hok hr.ok hr.effect

/-- The path and root ledger give precisely the conditional pair ledger
read by long and short pruning at the current partition. -/
theorem PathInv.pairs {G : Colored n k} {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : PathInv G ctx level st) (hp : PairsOk G ctx st) : LocalAutos ctx level st :=
  h.stab.toLocal hp

/-- The initial partition is its own stabilization frame and has no fixed vertices. -/
theorem initial_pathInv (G : Colored n k) (ctx : Ctx n) :
    PathInv G ctx 1 (initial n (initialPartition G).1 (initialPartition G).2) := by
  constructor
  · intro v hv hm
    change VSet.empty.mem v = true at hm
    simp at hm
  · exact PathStab.same (ctx := ctx)
      (st := (initial n (initialPartition G).1 (initialPartition G).2))

end Hex.GraphIso.Nauty
