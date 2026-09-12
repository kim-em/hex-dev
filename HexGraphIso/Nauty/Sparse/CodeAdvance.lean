/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeNode
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- First-child bookkeeping retains the actual settled comparisons. -/
theorem ReturnCodes.afterChild {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : ReturnCodes G cs bs fs st) (level tv : Nat) :
    ReturnCodes G cs bs fs (afterChildFirst level tv st) := h.fields rfl rfl rfl

/-- Resuming any completed child composes its comparison result with all
remaining native siblings. The actual exit determines whether to propagate
the result, consume short pruning, or restore the parent before continuing. -/
theorem codes_advance (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (tcLevel fuel cfuel numcells tc tv1 tv index : Nat) (first : Bool)
    (cs bs fs : List Nat) (cell : VSet n) (st : State n) (exit : Generic.Exit) (hl : 1 ≤ cs.length)
    (hr : ReturnCodes G.graph cs bs fs st)
    (h : CodeReady G tcLevel cs.length numcells ((policy (n := n)).recover (n + 2) cs.length st))
    (ht : Generic.Target State.frame cs.length tc cell ((policy (n := n)).recover (n + 2) cs.length st))
    (hrecord : CheapRecorded cs.length tc ((policy (n := n)).recover (n + 2) cs.length st))
    (hroute : RouteRecorded G.graph tcLevel cs.length tc ((policy (n := n)).recover (n + 2) cs.length st))
    (hpast : ∀ smaller : VSet n, Generic.Past first tv1 (smaller.nextElem (some tv)))
    (hfuel : n ≤ cs.length + fuel) (hcursor : n ≤ tv + (cfuel + 1)) :
    let out := (Generic.advance (n + 2)
      (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st)
      first cs.length numcells tc tv1 tv cell index st exit).2.2
    ∃ ds, ReturnCodes G.graph cs ds fs out ∧ Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
  let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
    Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      let out := (next first cs.length numcells tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) cs.length st)).2.2
      ∃ ds, ReturnCodes G.graph cs ds fs out ∧
        Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
    intro smaller hs index
    obtain ⟨ds, hr', hg⟩ := codes_sweep G hn tcLevel fuel (node_codes G hn tcLevel fuel) cfuel first
      cs bs fs numcells tc tv1 index _ smaller _ hl h (ht.subset hs)
      (fun _ hv => VSet.nextElem_mem hv) (hpast smaller) hrecord hroute hfuel
      (Generic.CursorFuel.next hcursor) (hr.recover (n + 2))
      (Or.inl (recover_nonpos hr.nonpos (n + 2) cs.length))
    rw [recover_key] at hg
    exact ⟨ds, hr', hg⟩
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      let out := (Generic.resume (n + 2) next first cs.length numcells tc tv1 tv smaller index st).2.2
      ∃ ds, ReturnCodes G.graph cs ds fs out ∧
        Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
    intro smaller hs
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hcontinue _ (fun _ hv => hs _ (Nauty.longprune_subset hv)) _
    · exact hcontinue smaller hs _
  cases exit with
  | fuel => exact ⟨bs, hr, Grows.refl _⟩
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact ⟨bs, hr, Grows.refl _⟩
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := st.frame) hv)
      · exact hresume cell (fun _ hv => hv)

end Hex.GraphIso.Nauty.Sparse
