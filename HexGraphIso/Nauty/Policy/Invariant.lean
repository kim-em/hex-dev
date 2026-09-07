/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Orbits
public import HexGraphIso.Nauty.Policy.Colors
public import HexGraphIso.Nauty.Policy.Store
public import HexGraphIso.Nauty.Policy.Workspace
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Persistent state after the first leaf. Partition frames and their
conditional descent histories belong to the individual call contract. -/
structure RunInv (G : Colored n k) (ctx : Ctx n) (st : Search n) : Prop where
  first : st.firstlab.toList.Perm (List.range n)
  canonical : st.canonlab.size = n ∧ CellsReach G st.canonlab
  cache : CanongInv ctx st.canong st.canonlab st.samerows
  scratch : st.workperm.size = n
  trace : TraceOk ctx st
  /-- Every orbit pointer is connected by recorded generators. -/
  orbits : OrbitsOk st
  /-- The saved first labelling respects the initial colour cells. -/
  firstReach : CellsReach G st.firstlab
  /-- Recorded generators stabilize the initial colour partition. -/
  colors : TraceStab G st
  /-- Every pruning pair has checked colour-preserving realizers. -/
  pairs : PairsOk G ctx st
  workspace : WorkspaceOk st.view

/-- The saved first permutation has exactly one entry for every vertex. -/
theorem RunInv.firstSize {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) : st.firstlab.size = n := by
  simpa only [Array.length_toList, List.length_range] using h.first.length_eq

/-- Frame receipts preserve the installed canonical labelling; reference,
cache and scratch facts assemble the persistent invariant at a return. -/
theorem RunInv.of_out {G : Colored n k} {ctx : Ctx n} {B level : Nat} {st out : Search n}
    (h : RunInv G ctx st) (hout : SearchOut G B level st.view out.view)
    (hfirst : out.firstlab = st.firstlab)
    (hcache : CanongInv ctx out.canong out.canonlab out.samerows)
    (hscratch : out.workperm.size = st.workperm.size) (htrace : TraceOk ctx out)
    (horbits : OrbitsOk out) (hcolors : TraceStab G out) (hpairs : PairsOk G ctx out)
    (hworkspace : WorkspaceOk out.view) :
    RunInv G ctx out := by
  refine ⟨by rw [hfirst]; exact h.first, ?_, hcache, hscratch.trans h.scratch, htrace, horbits,
    by rw [hfirst]; exact h.firstReach, hcolors, hpairs, hworkspace⟩
  rcases hout.canon with hc | hc
  · change out.canonlab = st.canonlab at hc
    rw [hc]
    exact h.canonical
  · exact hc

/-- Equal persistent fields retain the invariant during local bookkeeping. -/
theorem RunInv.congr {G : Colored n k} {ctx : Ctx n} {st out : Search n}
    (h : RunInv G ctx st) (hf : out.firstlab = st.firstlab) (hc : out.canonlab = st.canonlab)
    (hstore : CanongInv ctx out.canong out.canonlab out.samerows)
    (hw : out.workperm.size = st.workperm.size) (ht : out.genTrace = st.genTrace)
    (ho : out.orbits = st.orbits) (ha : out.autos = st.autos)
    (hcap : out.wsCap = st.wsCap) :
    RunInv G ctx out := by
  refine ⟨by rw [hf]; exact h.first, by rw [hc]; exact h.canonical,
    hstore, hw.trans h.scratch, ?_, h.orbits.congr ht ho, by rw [hf]; exact h.firstReach, h.colors.congr ht, h.pairs.congr ha, h.workspace.ofFields hcap ha⟩
  intro γ hγ
  rw [ht] at hγ
  exact h.trace γ hγ

/-- Node refinement preserves the persistent state. -/
theorem RunInv.visit {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (level numcells : Nat) :
    RunInv G ctx (Engine.visit ctx level numcells st).2.2 :=
  h.congr rfl rfl h.cache rfl rfl rfl rfl rfl

/-- Code comparison changes only comparison counters and the in-progress canonical codes. -/
theorem RunInv.compare {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (level code : Nat) :
    RunInv G ctx (compareCodes level code st) := by
  obtain ⟨_, _, hf, hc⟩ := compareCodes_frame level code st
  apply h.congr hf hc ((storePolicy ctx 0 0).compare level code st trivial h.cache)
    ((scratchPolicy ctx 0 0).compare level code st)
  all_goals unfold compareCodes
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.genTrace, apply_ite Search.orbits, apply_ite Search.autos, apply_ite Search.wsCap, ite_self]

/-- Off-path target selection preserves the persistent state. -/
theorem RunInv.target {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (tcLevel level numcells : Nat) :
    RunInv G ctx (chooseTarget false ctx tcLevel level numcells st).2.2.2 := by
  rw [chooseTarget_fields]
  exact h.congr rfl rfl h.cache rfl rfl rfl rfl rfl

/-- Classification updates the canonical row cache and retains the persistent state. -/
theorem RunInv.classify {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (level numcells : Nat) :
    RunInv G ctx (Engine.classify ctx level numcells st).2 := by
  obtain ⟨_, _, hf, hc⟩ := classify_frame ctx level numcells st
  exact h.congr hf hc (classify_store h.cache).1 (classify_workSize ctx level numcells st)
    (classify_trace ctx level numcells st) (classify_orbits ctx level numcells st) (classify_autos ctx level numcells st) (classify_capacity ctx level numcells st)

/-- Acting on a classification preserves the persistent state once admissions are checked. -/
theorem RunInv.leaf {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (h : RunInv G ctx st) (leaf : Leaf)
    (hok : SearchOk G level numcells st.view)
    (hnew : ∀ sr, leaf = .better sr → CanongInv ctx st.canong st.lab sr)
    (hcheck : leaf = .autoFirst ∨ leaf = .autoCanon → checkAutom ctx.g st.workperm = true)
    (hcolor : leaf = .autoFirst ∨ leaf = .autoCanon → ColorStab G st.workperm)
    (hn0 : 0 < n) (hboundary : Boundary G ctx level st) (hbound : st.noncheaplevel ≤ level) :
    RunInv G ctx (leafExit leaf level st).2 := by
  obtain ⟨hl, hp, hf, hc⟩ := leafExit_frame leaf level st
  exact h.of_out (frame_out (B := level) hok hl hp (Or.inl hf) hc) hf
    (leafExit_store ⟨h.cache, hnew⟩) (leafExit_workSize leaf level st)
    (leafExit_checked h.trace leaf hcheck) (h.orbits.leaf h.trace leaf level hcheck) (h.colors.leaf leaf level hcolor)
    (h.pairs.leaf hn0 leaf hcheck hcolor (hboundary.ready hbound)) (workspace_leaf h.workspace leaf level)

/-- The cheap-boundary update preserves persistent data. -/
theorem RunInv.cheap {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (first : Bool) (level : Nat) :
    RunInv G ctx (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl rfl h.cache rfl rfl rfl rfl rfl

/-- Individualizing a vertex changes no saved leaf or generator data. -/
theorem RunInv.child {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (first : Bool) (level tc tv : Nat) :
    RunInv G ctx (Engine.child first level tc tv st) := by
  cases first <;> exact h.congr rfl rfl h.cache rfl rfl rfl rfl rfl

/-- Removing the temporary fixed point preserves persistent data. -/
theorem RunInv.leave {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (tv : Nat) :
    RunInv G ctx { st with fixedpts := st.fixedpts.erase tv } :=
  h.congr rfl rfl h.cache rfl rfl rfl rfl rfl

/-- Recovering the parent partition does not alter saved leaves or generator data. -/
theorem RunInv.recover {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (inf level : Nat) :
    RunInv G ctx (recoverLevels level (recoverPtn inf level st)) := by
  have hr := (referencePolicy ctx inf 0).recover level st
  have hf := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2) hr
  have hc : (recoverLevels level (recoverPtn inf level st)).canonlab = st.canonlab := by
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.canonlab, ite_self]
  apply h.congr (out := recoverLevels level (recoverPtn inf level st)) hf hc ((storePolicy ctx inf 0).recover level st h.cache)
    ((scratchPolicy ctx inf 0).recover level st)
  all_goals unfold recoverLevels recoverPtn
  all_goals simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.genTrace, apply_ite Search.orbits, apply_ite Search.autos, apply_ite Search.wsCap, ite_self]

/-- Completing a sweep changes only its symmetry counter. -/
theorem RunInv.afterSweep {G : Colored n k} {ctx : Ctx n} {st : Search n}
    (h : RunInv G ctx st) (first : Bool) (level size index : Nat) :
    RunInv G ctx (Engine.afterSweep first level size index st) := by
  unfold Engine.afterSweep
  split <;> exact h.congr rfl rfl h.cache rfl rfl rfl rfl rfl

end Hex.GraphIso.Nauty.Engine
