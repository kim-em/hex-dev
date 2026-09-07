/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Trace
public import HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Every orbit pointer descends and is connected by a word of recorded generators. -/
def OrbitsOk (st : Search n) : Prop :=
  OrbSound (OrbConn st.genTrace.toList n) st.orbits n

/-- Preserving the generator trace and pointers preserves their relation. -/
theorem OrbitsOk.congr {st out : Search n} (h : OrbitsOk st)
    (ht : out.genTrace = st.genTrace) (ho : out.orbits = st.orbits) : OrbitsOk out := by
  unfold OrbitsOk
  rw [ht, ho]
  exact h

/-- Workspace replacement changes no orbit pointer. -/
theorem pushAuto_orbits (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).orbits = st.orbits := by
  unfold pushAuto
  split <;> rfl

/-- Admission joins the existing pointers with the scratch permutation. -/
theorem admit_orbits (st : Search n) :
    (admit st).orbits = (orbjoin st.orbits st.workperm n).1 := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

/-- Joining a checked admission preserves connectivity in the enlarged trace. -/
theorem OrbitsOk.admit {ctx : Ctx n} {st : Search n} (h : OrbitsOk st)
    (ht : TraceOk ctx st) (hwork : checkAutom ctx.g st.workperm = true) :
    OrbitsOk (Engine.admit st) := by
  have hv : ∀ γ ∈ (st.genTrace.push st.workperm).toList, checkAutom ctx.g γ = true := by
    intro γ hγ
    have hm : γ ∈ st.genTrace.push st.workperm := by simpa using hγ
    rcases Array.mem_push.mp hm with hm | rfl
    · exact ht γ hm
    · exact hwork
  unfold OrbitsOk
  rw [admit_trace, admit_orbits]
  apply orbjoin_orbConn (fun γ hγ => checkAutom_bound (hv γ hγ))
    (fun γ hγ => checkAutom_inj (hv γ hγ))
    (by simp)
  apply orbSound_orbConn_mono (gens := st.genTrace.toList) _ h
  intro γ hγ
  simp only [Array.toList_push, List.mem_append]
  exact Or.inl hγ

/-- The shared prune tail retains the generator trace and its orbit relation. -/
theorem OrbitsOk.prune {st : Search n} (h : OrbitsOk st) (level : Nat) :
    OrbitsOk (pruneReturn level st).2 := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · exact h.congr (pushAuto_trace _ _) (pushAuto_orbits _ _)
  · exact h

/-- The shared prune tail changes no orbit pointer. -/
theorem pruneReturn_orbits (level : Nat) (st : Search n) :
    (pruneReturn level st).2.orbits = st.orbits := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite Search.orbits, pushAuto_orbits, ite_self]

/-- Only the two automorphism verdicts join new orbit pointers. -/
theorem leafExit_orbits (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.orbits =
      match leaf with
      | .autoFirst | .autoCanon => (orbjoin st.orbits st.workperm n).1
      | _ => st.orbits := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite Search.orbits, admit_orbits, pruneReturn_orbits, install, ite_self]

/-- Every leaf action preserves pointer soundness once its admissions are checked. -/
theorem OrbitsOk.leaf {ctx : Ctx n} {st : Search n} (h : OrbitsOk st)
    (ht : TraceOk ctx st) (leaf : Leaf) (level : Nat)
    (hc : leaf = .autoFirst ∨ leaf = .autoCanon → checkAutom ctx.g st.workperm = true) :
    OrbitsOk (leafExit leaf level st).2 := by
  cases leaf
  all_goals first
    | simpa only [OrbitsOk, leafExit_trace, leafExit_orbits] using h
    | simpa only [OrbitsOk, leafExit_trace, leafExit_orbits, admit_trace, admit_orbits]
        using h.admit ht (hc (Or.inl rfl))
    | simpa only [OrbitsOk, leafExit_trace, leafExit_orbits, admit_trace, admit_orbits]
        using h.admit ht (hc (Or.inr rfl))

/-- Classification changes no orbit pointer, including when it fills the scratch array. -/
theorem classify_orbits (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.orbits = st.orbits := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.orbits, ite_self]

/-- Identity pointers are connected in the empty initial trace. -/
theorem initial_orbits (n : Nat) (lab0 : Array Nat) (cellEnds : List Nat) :
    OrbitsOk (initial n lab0 cellEnds) :=
  orbSound_orbConn_init []

end Hex.GraphIso.Nauty.Engine
