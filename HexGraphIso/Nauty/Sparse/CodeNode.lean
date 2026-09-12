/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeSweep
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every sufficiently bounded native off-path call returns settled code
comparisons and never decreases the incumbent. Its proof follows the
executed mutual recursion, including skipped siblings and nonlocal exits. -/
theorem node_codes (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel fuel : Nat) :
    ∀ cs bs fs numcells st, CodeEntry G tcLevel (cs.length + 1) numcells st →
      n ≤ cs.length + fuel → Comparison G.graph cs bs fs st →
      let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        (cs.length + 1) numcells st).2
      ∃ bs', ReturnCodes G.graph cs bs' fs out ∧
        Grows (State.key G.graph bs st) (State.key G.graph bs' out) := by
  induction fuel with
  | zero =>
    intro cs bs fs numcells st h hf hc
    have hb := Nat.le_trans h.node.ok.bc (bcount_le _ _ _)
    omega
  | succ fuel ih =>
    intro cs bs fs numcells st h hf hc
    let v := visit (.ofGraph G.graph) (cs.length + 1) numcells st
    let compared := compareCodes (cs.length + 1) v.2.1 v.2.2
    let target := chooseTarget false (.ofGraph G.graph) tcLevel (cs.length + 1) v.1 compared
    let classified := classify (.ofGraph G.graph) (cs.length + 1) v.1 target.2.2.2
    let acted := leafExit classified.1 (cs.length + 1) classified.2
    have hlen : cs.length ≤ n := by
      have hb := Nat.le_trans h.node.ok.bc (bcount_le _ _ _)
      omega
    have hcomp := (h.node.visit_ready hn (by omega)).compare v.2.1
    have ht : CodeReady G tcLevel (cs.length + 1) v.1 target.2.2.2 := h.prepare hn (by omega)
    have hm := hc.prepare tcLevel numcells hlen
    have hm' : Comparison G.graph (cs ++ [v.2.1]) bs fs target.2.2.2 := hm.1
    have hk : State.key G.graph bs target.2.2.2 = State.key G.graph bs st := hm.2
    have htarget := hcomp.ready.target hn (by omega) false tcLevel
    have hprefix : ∀ out, (∃ ds, ReturnCodes G.graph (cs ++ [v.2.1]) ds fs out ∧
        Grows (State.key G.graph bs target.2.2.2) (State.key G.graph ds out)) →
        ∃ ds, ReturnCodes G.graph cs ds fs out ∧
          Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
      intro out hout
      obtain ⟨ds, hr, hg⟩ := hout
      exact ⟨ds, hr.prefix ⟨[v.2.1], rfl⟩, hk ▸ hg⟩
    have hfinish : acted.1 = .done →
        let out := (Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
          (cs.length + 1) v.1 target.1.toNat ((target.2.1.nextElem none).getD 0)
          (target.2.1.nextElem none) target.2.1 0 (cheapCheck false (cs.length + 1) acted.2)).2.2
        ∃ ds, ReturnCodes G.graph cs ds fs out ∧
          Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
      intro hdone
      have hi : classified.1 = .internal := (leafExit_done classified.1 _ classified.2).mp hdone
      have he : acted.2 = target.2.2.2 := by
        change (leafExit (classify (.ofGraph G.graph) (cs.length + 1) v.1 target.2.2.2).1
          (cs.length + 1) (classify (.ofGraph G.graph) (cs.length + 1) v.1 target.2.2.2).2).2 = _
        rw [classify_internal_state hi]
        rfl
      have hopen : v.1 < n := by
        have hc := ht.ready.ok.count
        have hb := bcount_le target.2.2.2.ptn (cs.length + 1) n
        have hne := classify_open hi
        change v.1 = bcount target.2.2.2.ptn (cs.length + 1) n at hc
        omega
      obtain ⟨hrecord, hroute⟩ := h.recorded hn (by omega) hopen
      change CheapRecorded (cs.length + 1) target.1.toNat target.2.2.2 at hrecord
      change RouteRecorded G.graph tcLevel (cs.length + 1) target.1.toNat target.2.2.2 at hroute
      have hcheap := ht.ready.cheap false
      have hphase := hcomp.ready.target_phase (tcLevel := tcLevel) hn (by omega) hopen
      have hphase' : (cheapCheck false (cs.length + 1) target.2.2.2).compCanon ≤ 0 ∨
          false = false ∧ (target.2.1.nextElem none).isSome := by
        rcases hphase with hp | hp
        · left
          unfold cheapCheck
          split <;> exact hp
        · exact Or.inr ⟨rfl, hp⟩
      have hs := codes_sweep G hn tcLevel fuel ih (n + 1) false (cs ++ [v.2.1]) bs fs v.1
        target.1.toNat ((target.2.1.nextElem none).getD 0) 0 (target.2.1.nextElem none) target.2.1
        (cheapCheck false (cs.length + 1) target.2.2.2) (by simp)
        (by simpa only [List.length_append, List.length_singleton] using ht.cheap false)
        (by simpa only [List.length_append, List.length_singleton] using htarget.of_out hcheap.frame.effect)
        (fun _ hv => VSet.nextElem_mem hv) (by intro he; cases he)
        (by simpa only [List.length_append, List.length_singleton] using hrecord.cheap false ht.ancestor)
        (by simpa only [List.length_append, List.length_singleton] using hroute.cheap false)
        (by simp only [List.length_append, List.length_singleton]; omega) (fun _ _ => by omega)
        (by simpa only [List.length_append, List.length_singleton] using hm'.cheap false (cs.length + 1)) hphase'
      have hkey : State.key G.graph bs (cheapCheck false (cs.length + 1) target.2.2.2) =
          State.key G.graph bs target.2.2.2 := by unfold cheapCheck; split <;> rfl
      simp only [List.length_append, List.length_singleton, hkey] at hs
      rw [he]
      exact hprefix _ hs
    have hterminal : acted.1 ≠ .done →
        ∃ ds, ReturnCodes G.graph cs ds fs acted.2 ∧
          Grows (State.key G.graph bs st) (State.key G.graph ds acted.2) := by
      intro he
      have hi : classified.1 ≠ .internal := fun hi => he ((leafExit_done _ _ _).mpr hi)
      apply hprefix
      have hx := hm'.exit_returned
        (by simpa only [List.length_append, List.length_singleton] using ht.route)
        (by simpa only [List.length_append, List.length_singleton] using ht.toTraceReady)
        hn (by simp) (by simpa only [List.length_append, List.length_singleton] using hi)
      simpa only [List.length_append, List.length_singleton] using hx
    rw [Generic.node]
    unfold Generic.nodeStep
    let result := Id.run (do
      let (exit, prepared) := acted
      match exit with
      | .done => pure ()
      | _ => return (exit, prepared)
      let ready := cheapCheck false (cs.length + 1) prepared
      let s := Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        (cs.length + 1) v.1 target.1.toNat ((target.2.1.nextElem none).getD 0)
        (target.2.1.nextElem none) target.2.1 0 ready
      match s.1 with
      | .done => return (.unwind cs.length false,
          (policy (n := n)).afterSweep false (cs.length + 1) target.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2))
    change ∃ ds, ReturnCodes G.graph cs ds fs result.2 ∧
      Grows (State.key G.graph bs st) (State.key G.graph ds result.2)
    dsimp only [result]
    generalize he : acted = result at hfinish hterminal ⊢
    obtain ⟨exit, prepared⟩ := result
    cases exit with
    | fuel => exact hterminal (by intro he; cases he)
    | unwind => exact hterminal (by simp)
    | done =>
      have hs := hfinish rfl
      dsimp only
      generalize he : Generic.sweep false (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        (cs.length + 1) v.1 target.1.toNat ((target.2.1.nextElem none).getD 0)
        (target.2.1.nextElem none) target.2.1 0 (cheapCheck false (cs.length + 1) prepared) = result at hs ⊢
      obtain ⟨exit, index, out⟩ := result
      cases exit with
      | fuel => exact hs
      | unwind => exact hs
      | done =>
        obtain ⟨ds, hr, hg⟩ := hs
        refine ⟨ds, hr.afterSweep false (cs.length + 1) target.2.2.1 index, ?_⟩
        change Grows (State.key G.graph bs st)
          (State.key G.graph ds ((policy (n := n)).afterSweep false (cs.length + 1) target.2.2.1 index out))
        rwa [afterSweep_key]

end Hex.GraphIso.Nauty.Sparse
