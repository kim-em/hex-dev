/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstCheap
public import HexGraphIso.Nauty.Policy.Orbits
public import HexGraphIso.Nauty.Policy.FirstBoundary
import all HexGraphIso.Nauty.Policy.FirstCheap
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- The first descent begins before a reference leaf is installed. A previously
passed cheap guard supplies the small-cell invariant at its current node. -/
structure FirstPre (G : Colored n k) (ctx : Ctx n) (level numcells : Nat) (st : Search n) : Prop where
  positive : 1 ≤ level
  partition : SearchOk G level numcells st.view
  equitable : Equitable ctx level (st.refined ctx level numcells).lab (st.refined ctx level numcells).ptn
  codes : st.firstcode.size = n + 2
  targets : n < st.firsttc.size
  cache : st.canong.size = n
  scratch : st.workperm.size = n
  trace : TraceOk ctx st
  /-- Every orbit pointer is connected by recorded generators. -/
  orbits : OrbitsOk st
  /-- Recorded generators stabilize the initial colour partition. -/
  colors : TraceStab G st
  small : st.noncheaplevel < level → SubtreeOk ctx level (st.refined ctx level numcells)
  boundary : Boundary G ctx level st
  cheapBound : st.noncheaplevel ≤ level
  pairs : PairsOk G ctx st
  workspace : WorkspaceOk st.view
  path : PathInv G ctx level st
  starts : ∀ v, st.active.mem v = true → v = 0 ∨ st.ptn[v - 1]! ≤ level

/-- The chosen first child is a valid mathematical individualization step. -/
theorem firstChild_offset {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tv : Nat}
    {st : Search n} (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (htv : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let R := st.refined ctx level numcells
    ∃ e o, level < n ∧ (r.2.1.toNat, e) ∈ cells R.ptn level n ∧ r.2.1.toNat < e ∧
      o ≤ e - r.2.1.toNat ∧ R.lab[r.2.1.toNat + o]! = tv := by
  intro r R
  have hit := refined_iter (ctx := ctx) hn0 hlevel hok
  obtain ⟨hr, ht⟩ := prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hok
  obtain ⟨hl, hp, _⟩ := prepareFirst_fields ctx tcLevel level numcells st
  have hmem := VSet.nextElem_mem htv
  obtain ⟨len, htcell, hseg⟩ := ht
  obtain ⟨hcell, hlen, hrange⟩ := htcell (mem_ne_empty hmem)
  change r.2.1.toNat + len ≤ n at hrange
  obtain ⟨o, ho, hlabel⟩ := mem_segN_iff.mp (hseg tv hmem)
  change r.2.2.2.2.lab[r.2.1.toNat + o]! = tv at hlabel
  rw [hl] at hlabel
  have hcellR : IsCell R.ptn level r.2.1.toNat len := by
    change IsCell r.2.2.2.2.ptn level r.2.1.toNat len at hcell
    rwa [hp] at hcell
  have hc : (r.2.1.toNat, r.2.1.toNat + len - 1) ∈ cells R.ptn level n :=
    isCell_mem_cells hcellR (by rw [hit.ok.ptnSize]; exact Nat.le_refl _) hit.ok.ptnEnd (by omega)
  have hchild := firstChild_ok hn0 hlevel hok htv
  have hbc := hchild.bc
  have hb := bcount_le (Generic.Policy.child (n := n) true level r.2.1.toNat tv
    (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)).view.ptn (level + 1) n
  change level + 1 ≤ bcount (Generic.Policy.child (n := n) true level r.2.1.toNat tv
    (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)).view.ptn (level + 1) n at hbc
  exact ⟨r.2.1.toNat + len - 1, o, by omega, hc, by omega, by omega, hlabel⟩

/-- First-path preparation preserves allocation sizes and the existing generator trace. -/
theorem prepareFirst_stores (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    let out := (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2
    out.firstcode.size = st.firstcode.size ∧ out.firsttc.size = st.firsttc.size ∧
      out.canong = st.canong ∧ out.workperm.size = st.workperm.size ∧ out.genTrace = st.genTrace := by
  unfold Generic.prepareFirst
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.chooseTarget, Generic.Policy.recordFirst]
  rw [chooseFirst_fields]
  simp only [recordFirst, Array.size_set!]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- First-path preparation preserves the workspace before the first admission. -/
theorem prepareFirst_autos (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.autos = st.autos := by
  unfold Generic.prepareFirst
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.chooseTarget, Generic.Policy.recordFirst]
  rw [chooseFirst_fields]
  rfl

/-- First-path preparation keeps the configured workspace capacity. -/
theorem prepareFirst_capacity (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.wsCap = st.wsCap := by
  unfold Generic.prepareFirst
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.chooseTarget, Generic.Policy.recordFirst]
  rw [chooseFirst_fields]
  rfl

/-- First-path preparation preserves every previously frozen implicit pair. -/
theorem FirstPre.prepare_boundary {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (h : FirstPre G ctx level numcells st) (tcLevel : Nat) :
    Boundary G ctx level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2 := by
  have hv := h.boundary.visit (numcells := numcells) h.positive
  let r := visit ctx level numcells st
  have hr : Boundary G ctx level (recordFirst level r.2.1 r.2.2) := hv.congr rfl rfl rfl
  exact hr.target true tcLevel r.1

/-- First-path preparation refines the path and preserves it while recording codes and targets. -/
theorem FirstPre.prepare_path {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (h : FirstPre G ctx level numcells st) (hn0 : 0 < n)
    (hgsz : ctx.g.size = n) (tcLevel : Nat) :
    PathInv G ctx level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2 := by
  have hv := h.path.visit hn0 h.positive hgsz h.partition h.starts
  let r := visit ctx level numcells st
  have hr : PathInv G ctx level (recordFirst level r.2.1 r.2.2) := hv.fields rfl rfl rfl
  exact hr.target true tcLevel r.1

/-- The first-path guard validates the pair needed at the next child. -/
theorem FirstPre.cheap_boundary {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (h : FirstPre G ctx level numcells st) (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Boundary G ctx (level + 1)
      (cheapCheck true level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2) := by
  apply (h.prepare_boundary tcLevel).cheap true h.positive
  intro hguard
  obtain ⟨hl, hp, _⟩ := prepareFirst_fields ctx tcLevel level numcells st
  rw [hp] at hguard
  rw [hl, hp]
  exact refined_pair hn0 h.positive h.partition h.equitable hgsz hsymm hloop hguard

/-- A first-path child inherits the entry conditions, including the exact cheap boundary. -/
theorem FirstPre.child {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells tv : Nat}
    {st : Search n} (h : FirstPre G ctx level numcells st)
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (htv : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (hgsz : ctx.g.size = n)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    FirstPre G ctx (level + 1) (r.1 + 1)
      (Engine.child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) := by
  intro r
  let R := st.refined ctx level numcells
  let ready := cheapCheck true level r.2.2.2.2
  let ch := Engine.child true level r.2.1.toNat tv ready
  have hit := refined_iter (ctx := ctx) hn0 h.positive h.partition
  obtain ⟨e, o, hlevel, hcell, hne, ho, hlabel⟩ := firstChild_offset hn0 h.positive h.partition htv
  have hstep : ch.refined ctx (level + 1) (r.1 + 1) =
      childSt ctx level R r.2.1.toNat R.lab[r.2.1.toNat + o]! := by
    rw [firstChild_refined, ← hlabel]
  have hp := (prepareFirst_fields ctx tcLevel level numcells st).2.1
  have hacc := (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 h.positive h.partition).1.count
  change R.numcells = bcount r.2.2.2.2.ptn level n at hacc
  rw [hp] at hacc
  have hstores : ch.firstcode.size = st.firstcode.size ∧ ch.firsttc.size = st.firsttc.size ∧
      ch.canong = st.canong ∧ ch.workperm.size = st.workperm.size ∧ ch.genTrace = st.genTrace := by
    change ready.firstcode.size = st.firstcode.size ∧ ready.firsttc.size = st.firsttc.size ∧
      ready.canong = st.canong ∧ ready.workperm.size = st.workperm.size ∧ ready.genTrace = st.genTrace
    unfold ready cheapCheck
    split <;> exact prepareFirst_stores ctx tcLevel level numcells st
  have horbits : ch.orbits = st.orbits := by
    change ready.orbits = st.orbits
    unfold ready cheapCheck
    split <;> exact prepareFirst_orbits ctx tcLevel level numcells st
  refine ⟨by omega, firstChild_ok hn0 h.positive h.partition htv, ?_,
    hstores.1.trans h.codes, ?_, ?_, hstores.2.2.2.1.trans h.scratch, ?_, h.orbits.congr hstores.2.2.2.2 horbits, h.colors.congr hstores.2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hstep]
    exact equitable_breakout hit.ok.labSize hit.ok.ptnSize hit.ok.ptnEnd hit.valsWeak
      hit.ok.labOk hit.inj hsymm h.equitable hcell hne ho hacc.symm
  · rw [hstores.2.1]
    exact h.targets
  · rw [hstores.2.2.1]
    exact h.cache
  · intro γ hγ
    rw [hstores.2.2.2.2] at hγ
    exact h.trace γ hγ
  · intro hc
    have hsmall := firstCheap_small hn0 h.positive h.partition h.equitable h.small
      (show ready.noncheaplevel ≤ level from by change ready.noncheaplevel < level + 1 at hc; omega)
    rw [hstep]
    exact subtreeOk_child hsmall hlevel hsymm hcell hne ho

  · apply (h.cheap_boundary hn0 hgsz hsymm hloop).child true h.positive
    · exact ((prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 h.positive h.partition).2).of_out
        ((reachPolicy G ctx tcLevel hn0).cheap true level r.1 r.2.2.2.2
          (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 h.positive h.partition).1).effect
    · exact VSet.nextElem_mem htv
  · change ready.noncheaplevel ≤ level + 1
    apply cheap_bound true
    rw [prepareFirst_noncheap]
    exact h.cheapBound

  · apply h.pairs.congr
    change ready.autos = st.autos
    unfold ready cheapCheck
    split <;> exact prepareFirst_autos ctx tcLevel level numcells st

  · apply h.workspace.ofFields
    · change ready.wsCap = st.wsCap
      unfold ready cheapCheck
      split <;> exact prepareFirst_capacity ctx tcLevel level numcells st
    · change ready.autos = st.autos
      unfold ready cheapCheck
      split <;> exact prepareFirst_autos ctx tcLevel level numcells st

  · have hp := (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 h.positive h.partition)
    have hc := (reachPolicy G ctx tcLevel hn0).cheap true level r.1 r.2.2.2.2 hp.1
    exact ((h.prepare_path hn0 hgsz tcLevel).cheap true).child true hn0 h.positive hc.ok
      (hp.2.of_out hc.effect) (VSet.nextElem_mem htv)
  · have hp := (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 h.positive h.partition)
    have hc := (reachPolicy G ctx tcLevel hn0).cheap true level r.1 r.2.2.2.2 hp.1
    exact child_starts true (hp.2.of_out hc.effect) (VSet.nextElem_mem htv)

end Hex.GraphIso.Nauty.Engine
