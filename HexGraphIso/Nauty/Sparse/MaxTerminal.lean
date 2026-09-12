/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxContext
public import HexGraphIso.Nauty.Sparse.MaxCheap
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.CodeScope
import all HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A native bad verdict cannot follow a positive code comparison. -/
theorem bad_nonpos {g : Graph n} {level numcells : Nat} {st : State n}
    (h : (classify g level numcells st).1 = .bad) : st.compCanon ≤ 0 := by
  by_cases hc : st.compCanon ≤ 0
  · exact hc
  have hp : 0 < st.compCanon := by omega
  unfold classify at h
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, scatter_eq,
    show ¬st.compCanon < 0 by omega, decide_false, Bool.and_false, Bool.false_eq_true,
    beq_eq_false_iff_ne.mpr (show st.compCanon ≠ 0 by omega), hp, ite_true] at h
  repeat' split at h
  all_goals cases h <;> contradiction

/-- Native row classification retains the first divergent code level. -/
theorem classify_eqlevCanon (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.eqlevCanon = st.eqlevCanon := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.eqlevCanon, ite_self]

/-- A better native verdict occurs only at a discrete leaf. -/
theorem better_discrete {g : Graph n} {level numcells sr : Nat} {st : State n}
    (h : (classify g level numcells st).1 = .better sr) : numcells = n := by
  by_cases hn : numcells = n
  · exact hn
  rw [classify_eq] at h
  split at h
  · cases h
  · simp only [bne_iff_ne.mpr hn, ite_true] at h
    cases h

namespace Max

/-- Installing a better leaf resets code agreement to its depth; any
strict-ancestor return therefore names the actual cheap boundary. -/
theorem better_target {level sr target : Nat} {short : Bool} {st : State n}
    (he : (leafExit (.better sr) level st).1 = .unwind target short)
    (ht : target < level) : target = st.noncheaplevel - 1 := by
  unfold leafExit at he
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst] at he
  split at he
  all_goals
    obtain ⟨t, s, hx, hbound⟩ := pruneReturn_target level (install level sr _)
    rw [he] at hx
    cases hx
    change level ≤ target ∨ target = st.noncheaplevel - 1 at hbound
    exact hbound.resolve_left (by omega)

/-- Native rejection satisfies the full return contract at discrete and
nondiscrete nodes. A nonlocal code return carries a negative prefix;
every other nonlocal return propagates coverage through cheap ancestors. -/
theorem NodeInput.bad {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {short : Bool}
    (h : NodeInput G tcLevel f bs fs parents)
    (hbad : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .bad)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind target short) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  have hfirst : f.entry.gcaFirst < f.level := by have := h.counters; omega
  by_cases hd : p.1 = n
  · obtain ⟨_, _, hb, hc⟩ := h.frame.leaf_bound h.codes h.machine hd
    have ht : target < f.level := prepared_bound hfirst h.counters.2.2 h.pairs.bound hexit
    refine ⟨hb, ?_⟩
    rw [hexit]
    refine ⟨by omega, ?_⟩
    split
    · exact hc
    · rename_i hne
      have hbelow : target < f.level - 1 := by omega
      have he : (leafExit .bad f.level c.2).1 = .unwind target short := by
        change (leafExit c.1 f.level c.2).1 = .unwind target short at hexit
        rwa [hbad] at hexit
      rcases bad_target he with hcode | hcheap
      · have hce : c.2.eqlevCanon = p.2.2.2.2.2.eqlevCanon := classify_eqlevCanon _ _ _ _
        rw [hce] at hcode
        have hlen := h.frame.length
        have hdepth := h.frame.depth
        have hm := h.machine.prepare tcLevel f.numcells (by omega)
        rw [hlen] at hm
        have hcomparison : Comparison G.graph (f.codes ++ [f.code G.graph]) bs fs p.2.2.2.2.2 := hm.1
        have hlength : (f.codes ++ [f.code G.graph]).length = f.level := by
          simp only [List.length_append, List.length_singleton, hlen]
        have hn : p.2.2.2.2.2.compCanon ≤ 0 := bad_nonpos hbad
        have hneg : p.2.2.2.2.2.compCanon < 0 := by
          rcases hcomparison.canonical.tri with ⟨_, he, _⟩ | ⟨j, _, _, _, _, _, hh⟩
          · rw [hlength] at he
            rw [he] at hcode
            change f.level ≤ target at hcode
            omega
          · rcases hh with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
        have hw := (h.scope.codes.push h.frame).rejected (tcLevel := tcLevel)
          (by rw [hlength]; omega) hcomparison hneg hcode
        have hw' := (Max.Witness.below hbelow).mp hw
        rw [hm.2] at hw'
        exact hw'.grow hb.grows
      · have hnc := f.emit_noncheap G.graph tcLevel
        have he : (f.emit G.graph tcLevel).2.noncheaplevel = c.2.noncheaplevel := leafExit_noncheap c.1 f.level c.2
        exact h.scope.cheap_witness hbelow (by omega) hc hb.grows
  · exact h.frame.prune h.scope h.machine hfirst h.counters.2.2 h.pairs.bound hexit hd hbad

/-- A better native leaf satisfies the full maximum return contract,
including its nonlocal cheap-boundary return. -/
theorem NodeInput.better {G : GraphIso.Sparse.Colored n k} {tcLevel target sr : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n} {short : Bool}
    (h : NodeInput G tcLevel f bs fs parents)
    (hbetter : let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .better sr)
    (hexit : (f.emit G.graph tcLevel).1 = .unwind target short) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  have hfirst : f.entry.gcaFirst < f.level := by have := h.counters; omega
  have ht : target < f.level := prepared_bound hfirst h.counters.2.2 h.pairs.bound hexit
  apply h.frame.cheap_leaf h.scope h.codes h.machine (better_discrete hbetter)
    hfirst h.counters.2.2 h.pairs.bound hexit
  change target = (leafExit c.1 f.level c.2).2.noncheaplevel - 1
  rw [leafExit_noncheap]
  apply better_target (ht := ht)
  change (leafExit c.1 f.level c.2).1 = .unwind target short at hexit
  rwa [hbetter] at hexit

/-- Every terminal native classifier branch now discharges the complete
node return rule under the single assembled traversal context. -/
theorem NodeInput.emit {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G tcLevel f bs fs parents) (he : (f.emit G.graph tcLevel).1 ≠ .done) :
    MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (f.emit G.graph tcLevel).2) (f.level - 1)
      (Max.Witness G tcLevel parents.frames) (f.emit G.graph tcLevel).1 := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2
  have hnf : (f.emit G.graph tcLevel).1 ≠ .fuel := leafExit_noFuel c.1 f.level c.2
  obtain ⟨target, short, hx⟩ : ∃ target short, (f.emit G.graph tcLevel).1 = .unwind target short := by
    cases hx : (f.emit G.graph tcLevel).1 with
    | done => exact (he hx).elim
    | fuel => exact (hnf hx).elim
    | unwind target short => exact ⟨target, short, rfl⟩
  cases hc : c.1 with
  | internal => exact (he ((leafExit_done c.1 f.level c.2).mpr hc)).elim
  | bad => exact h.bad hc hx
  | better sr => exact h.better hc hx
  | autoFirst =>
    exact h.frame.auto_first h.codes h.machine h.scope h.guides h.counters.1
      (by have := h.counters; omega) hc
  | autoCanon =>
    exact h.frame.canonical h.codes h.machine h.scope h.guides h.cosets h.ranked h.traces h.orbits h.counters hc

end Max
end Hex.GraphIso.Nauty.Sparse
