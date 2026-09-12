/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Reach
public import HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The production frame contract with conditional absence of exhaustion.
The existing level and cursor bounds suffice; truncated calls retain frames. -/
@[expose] def fuelContract (G : GraphIso.Sparse.Colored n k) : Generic.Contract (State n) n where
  nodePre := (reachContract G).nodePre
  nodePost fuel first level numcells st out :=
    (reachContract G).nodePost fuel first level numcells st out ∧
      (n + 1 ≤ level + fuel → out.1 ≠ .fuel)
  sweepPre := (reachContract G).sweepPre
  sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st out :=
    (reachContract G).sweepPost fuel cfuel first level numcells tc tv1 cursor cell index st out ∧
      (n ≤ level + fuel → Generic.CursorFuel n cfuel cursor → out.1 ≠ .fuel)

theorem fuel_node_reach {G : GraphIso.Sparse.Colored n k} {fuel : Nat} {f : Generic.NodeFn (State n)}
    (h : (fuelContract G).nodeValid fuel f) : (reachContract G).nodeValid fuel f :=
  fun first level numcells st hin => (h first level numcells st hin).1

theorem fuel_sweep_reach {G : GraphIso.Sparse.Colored n k} {fuel cfuel : Nat}
    {f : Generic.SweepFn (State n) n} (h : (fuelContract G).sweepValid fuel cfuel f) :
    (reachContract G).sweepValid fuel cfuel f :=
  fun first level numcells tc tv1 cursor cell index st hin =>
    (h first level numcells tc tv1 cursor cell index st hin).1

/-- Local refinement and classification cannot exhaust the remaining node
budget. Every recursive sweep receives a valid equitable parent and cursor. -/
theorem fuel_node (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel : Nat)
    {fuel : Nat} {next : Generic.SweepFn (State n) n}
    (hnext : (fuelContract G).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n)
    (hl : 1 ≤ level) (h : NodeInv G level numcells st) (hf : n + 1 ≤ level + (fuel + 1)) :
    (Generic.nodeStep (.ofGraph G.graph) tcLevel next first level numcells st).1 ≠ .fuel := by
  have hv := h.visit_ready hn hl
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.compareCodes,
    Generic.Policy.chooseTarget, Generic.Policy.firstterminal, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck]
  generalize he : visit (.ofGraph G.graph) level numcells st = r at hv ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then recordFirst level code refined else compareCodes level code refined
  have hc : Local G level nc refined compared := by
    cases first
    · exact hv.compare code
    · exact hv.record code
  have ht := hc.ready.target_frame first tcLevel
  have htarget := hc.ready.target hn hl first tcLevel
  dsimp only
  generalize he : chooseTarget first (.ofGraph G.graph) tcLevel level nc compared = r at ht htarget ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have hfinish : ∀ prepared, Ready G level nc prepared →
      Generic.Target State.frame level tc.toNat cell prepared →
      (Id.run (do
        let ready := cheapCheck first level prepared
        let tv := cell.nextElem none
        let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 ready
        match exit with
        | .done => return (Generic.Exit.unwind (level - 1) false,
            Generic.Policy.afterSweep (n := n) first level size index out)
        | _ => return (exit, out))).1 ≠ .fuel := by
    intro prepared hp htarg
    have hcheap := hp.cheap first
    have hsafe := (hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 _
      ⟨hl, hcheap.ready, htarg.of_out hcheap.frame.effect, fun _ hv => VSet.nextElem_mem hv⟩).2
      (by omega) (fun _ _ => by omega)
    dsimp only
    generalize he : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck first level prepared) = r at hsafe ⊢
    obtain ⟨exit, index, out⟩ := r
    cases exit <;> simp_all
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
    split
    · simp
    · exact hfinish targeted ht.ready htarget
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hc' := ht.ready.classify
    generalize he : classify (.ofGraph G.graph) level nc targeted = r at hc' ⊢
    obtain ⟨leaf, classified⟩ := r
    have he' := hc'.ready.leaf leaf
    have hsafe := leafExit_noFuel leaf level classified
    generalize he : leafExit leaf level classified = r at he' hsafe ⊢
    obtain ⟨exit, out⟩ := r
    cases exit with
    | done => exact hfinish out he'.ready ((htarget.of_out hc'.frame.effect).of_out he'.frame.effect)
    | unwind => simp
    | fuel => exact (hsafe rfl).elim

end Hex.GraphIso.Nauty.Sparse
