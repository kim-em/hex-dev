/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceState
import all HexGraphIso.Nauty.Policy.Generic.Reference
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Later siblings preserve trace soundness from the smaller-depth node
induction hypothesis. Every resumption reconstructs its native history and
target membership after the actual filters and recovery. -/
theorem trace_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel fuel : Nat)
    (hd : ∀ level numcells st, 1 ≤ level → TraceEntry G tcLevel level numcells st →
      TraceOk G (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2)
    (cfuel : Nat) (first : Bool) (level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hl : 1 ≤ level)
    (h : TraceReady G tcLevel level numcells st) (ht : Generic.Target State.frame level tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) (hpast : Generic.Past first tv1 cursor)
    (hrecord : CheapRecorded level tc st) :
    TraceOk G (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells
      tc tv1 cursor cell index st).2.2 := by
  induction cfuel generalizing cursor cell index st with
  | zero => cases cursor <;> rw [Generic.sweep] <;> exact h.trace
  | succ cfuel ih =>
    cases cursor with
    | none => rw [Generic.sweep]; exact h.trace
    | some tv =>
      have hmem := hv tv rfl
      have hp : ∀ smaller : VSet n, Generic.Past first tv1 (smaller.nextElem (some tv)) := by
        intro smaller hf v hnext
        have hbase := hpast hf tv rfl
        have hnext := (VSet.nextElem_eq_some_iff.mp hnext).2.1
        change tv + 1 ≤ v at hnext
        omega
      have hf : (first && tv == tv1) = false := by
        cases first with
        | false => rfl
        | true =>
          have hb := hpast rfl tv rfl
          simp only [Bool.true_and, beq_eq_false_iff_ne]
          omega
      let ch := (policy (n := n)).child first level tc tv st
      let raw := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch
      let left := (policy (n := n)).leaveChild tv raw.2
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
      have hch := h.child hn hl first ht hmem hrecord
      have htrace : TraceOk G raw.2 := hd _ _ _ (by omega) hch
      have hback := h.child_return hn hl first fuel ht hmem htrace
      have hframe := h.ready.child_frame hn hl first ht hmem
        (by simpa only [Nat.add_sub_cancel] using
          node_frame G hn false tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hch.node)
      have hrestore := (h.ready.recover hn hl (hframe.leave tv)).2
      have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
          TraceOk G (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index
            ((policy (n := n)).recover (n + 2) level left)).2.2 := by
        intro smaller hs index
        exact ih index _ smaller _ hback.1 ((ht.subset hs).of_out hrestore.effect)
          (fun _ hv => VSet.nextElem_mem hv) (hp smaller) (hback.2 hrecord)
      have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
          TraceOk G (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index left).2.2 := by
        intro smaller hs
        unfold Generic.resume
        simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
        split
        · exact hcontinue _ (fun _ hv => hs _ (Nauty.longprune_subset hv)) _
        · exact hcontinue smaller hs _
      have hadv : TraceOk G (Generic.advance (n + 2) next first level numcells tc tv1 tv cell index left raw.1).2.2 := by
        cases raw.1 with
        | fuel => exact htrace.leave tv
        | done => exact hresume cell (fun _ hv => hv)
        | unwind target short =>
          unfold Generic.advance
          simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
          split
          · exact htrace.leave tv
          · split
            · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := left.frame) hv)
            · exact hresume cell (fun _ hv => hv)
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hf, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact hadv
      · exact ih _ _ cell st h ht (fun _ hv => VSet.nextElem_mem hv) (hp cell) hrecord

end Hex.GraphIso.Nauty.Sparse
