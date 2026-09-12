/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.EarlyReturn
public import HexGraphIso.Nauty.Sparse.CanonScatter
public import HexGraphIso.Nauty.Sparse.Saved
public import HexGraphIso.Nauty.Sparse.Pairs
public import HexGraphIso.Nauty.Policy.Reference.Return
import all HexGraphIso.Nauty.Sparse.Classify
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Sparse.EarlyReturn
import all HexGraphIso.Nauty.Policy.Reference.Return
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- First-reference classification supplies the full scatter map from
the returned native state, including its actual work-array allocation. -/
theorem classify_first_map {g : Graph n} {level numcells : Nat} {before out : State n}
    (hc : classify g level numcells before = (.autoFirst, out))
    (hw : out.workperm.size = n) (hf : out.firstlab.size = n)
    (hp : out.firstlab.toList.Perm (List.range n)) :
    ∀ i, i < n → out.workperm[out.firstlab[i]!]! = out.lab[i]! := by
  obtain ⟨_, _, he, _⟩ := classify_first hc
  rw [he] at hw hf hp ⊢
  have hws : before.workperm.size = n := (scatter_size _ _).symm.trans hw
  exact scatter_map hws hf hp

/-- Every native automorphism verdict retains its emitted reference
carrier or a strictly smaller orbit image, including canonical admissions
that do not merge an orbit. The trace and label validity come from the
executed call's already established soundness invariants. -/
theorem leaf_refReturn {G : GraphIso.Sparse.Colored n k} {level numcells target : Nat}
    {before : State n} {short : Bool} (hn : 0 < n)
    (ha : (classify (.ofGraph G.graph) level numcells before).1 = .autoFirst ∨
      (classify (.ofGraph G.graph) level numcells before).1 = .autoCanon)
    (he : (leafExit (classify (.ofGraph G.graph) level numcells before).1 level
      (classify (.ofGraph G.graph) level numcells before).2).1 = .unwind target short)
    (hs : Saved G (leafExit (classify (.ofGraph G.graph) level numcells before).1 level
      (classify (.ofGraph G.graph) level numcells before).2).2)
    (ht : TraceOk G (leafExit (classify (.ofGraph G.graph) level numcells before).1 level
      (classify (.ofGraph G.graph) level numcells before).2).2) :
    RefReturn (Graph.context G.graph) target (leafExit
      (classify (.ofGraph G.graph) level numcells before).1 level
      (classify (.ofGraph G.graph) level numcells before).2).2 := by
  let c := classify (.ofGraph G.graph) level numcells before
  let out := (leafExit c.1 level c.2).2
  have hwork : out.workperm = c.2.workperm := leafExit_workperm ..
  have htrace : c.2.workperm ∈ out.genTrace := by
    dsimp only [out]
    rw [leafExit_trace]
    rcases ha with ha | ha <;> change c.1 = _ at ha <;> rw [ha] <;> exact Array.mem_push_self
  have hcheck := (ht _ htrace).checked
  have hsize : c.2.workperm.size = n := hwork ▸ hs.work
  have hlab : out.lab = c.2.lab := (leafExit_frame ..).1
  rcases ha with ha | ha
  · change c.1 = .autoFirst at ha
    have hf : out.firstlab = c.2.firstlab := (leafExit_frame ..).2.2.1
    have hm := classify_first_map (Prod.ext ha rfl) hsize (hf ▸ hs.first.1)
      (hf ▸ isPerm_of_cellsReach hs.first.1 hn hs.first.2)
    refine .first ?_ ⟨c.2.workperm, htrace, hcheck, ?_⟩
    · change target = (leafExit c.1 level c.2).2.gcaFirst
      rw [leafExit_gca]
      change (leafExit c.1 level c.2).1 = _ at he
      rw [ha] at he
      unfold leafExit at he
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
      split at he <;> cases he <;> rw [admit_gca]
    · rw [hf, hlab]
      exact hm
  · change c.1 = .autoCanon at ha
    have hf : out.canonlab = c.2.canonlab := by dsimp only [out]; rw [ha, autoCanon_ref]
    have hp : out.canonlab.toList.Perm (List.range n) :=
      isPerm_of_cellsReach hs.canonical.1 hn hs.canonical.2
    have hm := classify_canon_out (g := .ofGraph G.graph) (level := level) (numcells := numcells)
      (st := before) (show c.1 = .autoCanon from ha) hsize (hf ▸ hs.canonical.1) (hf ▸ hp)
    have hcarrier : LabelCarrier (Graph.context G.graph) out.canonlab out.lab out.genTrace :=
      ⟨c.2.workperm, htrace, hcheck, by rw [hf, hlab]; exact hm⟩
    change (leafExit c.1 level c.2).1 = _ at he
    rw [ha] at he
    change RefReturn (Graph.context G.graph) target (leafExit c.1 level c.2).2
    rw [ha]
    change LabelCarrier (Graph.context G.graph) (leafExit c.1 level c.2).2.canonlab
      (leafExit c.1 level c.2).2.lab (leafExit c.1 level c.2).2.genTrace at hcarrier
    rw [ha] at hcarrier
    unfold leafExit at he hcarrier ⊢
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd] at he hcarrier ⊢
    repeat' split at he
    all_goals cases he
    all_goals simp_all only [↓reduceIte]
    all_goals first | exact .canon rfl hcarrier | exact .orbit rfl (by assumption)

/-- An unconsumed native return above both subtree boundaries retains
the reference or orbit evidence through all fixed-point cleanup. -/
theorem EarlyReturn.reference {G : GraphIso.Sparse.Colored n k} {target bound : Nat}
    {short : Bool} {out : State n} (h : EarlyReturn (.ofGraph G.graph) target short out)
    (hn0 : 0 < n) (hs : Saved G out) (ht : TraceOk G out)
    (hb : target < bound) (hn : bound < out.noncheaplevel) (ha : bound < out.allsamelevel) :
    RefReturn (Graph.context G.graph) target out := by
  obtain ⟨level, numcells, before, he, hstate⟩ := h
  let c := classify (.ofGraph G.graph) level numcells before
  let emitted := leafExit c.1 level c.2
  have hauto : c.1 = .autoFirst ∨ c.1 = .autoCanon := by
    by_cases hf : c.1 = .autoFirst
    · exact Or.inl hf
    by_cases hc : c.1 = .autoCanon
    · exact Or.inr hc
    have hbound := leaf_boundary hf hc he
    rw [hstate] at hn ha
    change bound < emitted.2.noncheaplevel at hn
    change bound < emitted.2.allsamelevel at ha
    change emitted.2.noncheaplevel ≤ target + 1 ∨ emitted.2.allsamelevel ≤ target + 1 at hbound
    omega
  have hstored : Saved G emitted.2 := by
    rw [hstate] at hs
    exact ⟨hs.first, hs.canonical, hs.store, hs.work⟩
  have htrace : TraceOk G emitted.2 := by
    rw [hstate] at ht
    exact ht.congr rfl
  have hr := leaf_refReturn hn0 hauto he hstored htrace
  rw [hstate]
  exact hr.fixed _

/-- The actual sparse off-path call never requests short pruning at its
positive first ancestor. This includes arbitrarily deep emitted returns. -/
theorem node_short_first {g : Graph n} {inf tcLevel fuel level numcells target : Nat}
    {st : State n} (hpos : 0 < target)
    (he : (Generic.node false g inf tcLevel fuel level numcells st).1 = .unwind target true) :
    target ≠ st.gcaFirst := by
  obtain ⟨depth, cells, before, hemit, hs⟩ := node_short_early g inf tcLevel fuel level numcells st he
  have hh := leaf_short_first hpos hemit
  have hg := node_gca g inf tcLevel fuel level numcells st
  rw [hs] at hg
  change (leafExit (classify g depth cells before).1 depth (classify g depth cells before).2).2.gcaFirst = st.gcaFirst at hg
  rwa [hg] at hh

end Hex.GraphIso.Nauty.Sparse
