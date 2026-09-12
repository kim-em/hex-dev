/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Pairs
public import HexGraphIso.Nauty.Sparse.CodePrefix
public import HexGraphIso.Nauty.Invariant.Carrier
public import HexGraphIso.Nauty.Sparse.ReferenceCode
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Sparse.Classify
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Matching native leaf graphs force first-reference admission. The
actual scatter is appended to the unbounded trace and maps the saved label
to the returned label, whether the cheap guard or adjacency scan accepts. -/
theorem rows_emit {G : GraphIso.Sparse.Colored n k} {level : Nat} {st : State n}
    {f l : Label n} (hw : st.workperm.size = n)
    (hf : Label.ofArray? n st.firstlab = some f) (hl : Label.ofArray? n st.lab = some l)
    (hrf : CellsReach G.toDense st.firstlab) (hrl : CellsReach G.toDense st.lab)
    (hrows : G.graph.relabel l.perm = G.graph.relabel f.perm) (heq : st.eqlevFirst = level) :
    let c := classify (.ofGraph G.graph) level n st
    let out := leafExit c.1 level c.2
    c.1 = .autoFirst ∧ out.1 = .unwind st.gcaFirst false ∧
      LabelCarrier (Graph.context G.graph) st.firstlab out.2.lab out.2.genTrace := by
  have hp := label_pair_iso G hl hf hrl hrf hrows
  have hs := scatter_perm hw hf hl
  have hi : isautom (.ofGraph G.graph) (scatter st.firstlab st).workperm = true :=
    (isautom_iff G.graph _ _ hs).mpr hp.adj_eq
  have ha : Automorphism G (scatter st.firstlab st).workperm :=
    ⟨by rw [scatter_size, hw], _, hp, hs⟩
  have hclass : classify (.ofGraph G.graph) level n st = (.autoFirst, scatter st.firstlab st) := by
    rw [classify_eq]
    simp only [heq, beq_self_eq_true, bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
      ite_false, ite_true, hi, Bool.or_true]
  dsimp only
  rw [hclass]
  refine ⟨rfl, ?_, ?_⟩
  · unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, admit_gca]
    split <;> rfl
  · refine ⟨(scatter st.firstlab st).workperm, ?_, ha.checked, ?_⟩
    · rw [leafExit_trace]
      exact Array.mem_push_self
    · rw [(leafExit_frame .autoFirst level (scatter st.firstlab st)).1]
      intro i hi
      change (scatter st.firstlab st).workperm[st.firstlab[i]!]! = st.lab[i]!
      rw [← Label.ofArray?_get hf i hi]
      rw [hs]
      simpa only [Label.get, Perm.get_comp, Perm.inv_get_get] using Label.ofArray?_get hl i hi

/-- A matching discrete visit emits its reference carrier in the actual
native node call, including cached refinement and code comparison. -/
theorem matching_leaf {G : GraphIso.Sparse.Colored n k} {inf tcLevel fuel level numcells : Nat}
    {st : State n} {f l : Label n} (hn : 0 < n) (hlevel : 1 ≤ level)
    (hnode : NodeInv G level numcells st) (hw : st.workperm.size = n)
    (hf : Label.ofArray? n st.firstlab = some f) (hrf : CellsReach G.toDense st.firstlab)
    (hl : Label.ofArray? n (State.refined (.ofGraph G.graph) level numcells st).lab = some l)
    (hnum : (State.refined (.ofGraph G.graph) level numcells st).numcells = n)
    (hcode : (State.refined (.ofGraph G.graph) level numcells st).longcode = st.firstcode[level]!)
    (hrows : G.graph.relabel l.perm = G.graph.relabel f.perm)
    (heq : st.eqlevFirst = level - 1) :
    let out := Generic.node false (.ofGraph G.graph) inf tcLevel (fuel + 1) level numcells st
    out.1 = .unwind st.gcaFirst false ∧
      LabelCarrier (Graph.context G.graph) st.firstlab out.2.lab out.2.genTrace := by
  let rs := State.refined (.ofGraph G.graph) level numcells st
  let visited := (visit (.ofGraph G.graph) level numcells st).2.2
  let compared := compareCodes level rs.longcode visited
  have hfields : compared.lab = rs.lab ∧ compared.firstlab = st.firstlab ∧
      compared.workperm = st.workperm ∧ compared.gcaFirst = st.gcaFirst := by
    dsimp only [compared]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run]
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  have hc : compared.eqlevFirst = level := by
    rw [compareCodes_eqlev]
    change (if st.eqlevFirst = level - 1 ∧ rs.longcode = st.firstcode[level]!
      then level else st.eqlevFirst) = level
    rw [ite_eq_left ⟨heq, hcode⟩]
  have hready := hnode.visit_ready hn hlevel
  have emit := rows_emit (G := G) (hfields.2.2.1 ▸ hw) (hfields.2.1 ▸ hf)
    (hfields.1 ▸ hl) (hfields.2.1 ▸ hrf) (hfields.1 ▸ hready.ok.reach) hrows hc
  let c := classify (.ofGraph G.graph) level n compared
  let result := leafExit c.1 level c.2
  have hret : result.1 = .unwind st.gcaFirst false := emit.2.1.trans (by rw [hfields.2.2.2])
  have ht : chooseTarget false (.ofGraph G.graph) tcLevel level n compared =
      (-1, VSet.empty, 0, compared) := by simp [chooseTarget]
  have hcall : Generic.node false (.ofGraph G.graph) inf tcLevel (fuel + 1) level numcells st = result := by
    rw [Generic.node]
    simp only [Generic.nodeStep, Bool.false_eq_true, ite_false]
    change (Id.run do
      let t := chooseTarget false (.ofGraph G.graph) tcLevel level rs.numcells compared
      let c := classify (.ofGraph G.graph) level rs.numcells t.2.2.2
      let result := leafExit c.1 level c.2
      match result.1 with
      | .done =>
        let s := Generic.sweep false (.ofGraph G.graph) inf tcLevel fuel (n + 1)
          level rs.numcells t.1.toNat ((t.2.1.nextElem none).getD 0)
          (t.2.1.nextElem none) t.2.1 0 (cheapCheck false level result.2)
        match s.1 with
        | .done => pure (.unwind (level - 1) false,
            (policy (n := n)).afterSweep false level t.2.2.1 s.2.1 s.2.2)
        | _ => pure (s.1, s.2.2)
      | _ => pure result) = result
    rw [hnum, ht]
    change (match result.1 with | .done => _ | _ => result) = result
    rw [hret]
  dsimp only
  rw [hcall]
  exact ⟨hret, hfields.2.1 ▸ emit.2.2⟩

end Hex.GraphIso.Nauty.Sparse
