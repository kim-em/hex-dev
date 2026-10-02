/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodePrepare
public import HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.Generic.Reference
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Later native siblings compose incumbent growth and return settled
comparisons on an extension of the parent's code path. The proof follows
the actual short/long filters, nonlocal returns, and partition recovery. -/
theorem codes_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel fuel : Nat)
    (hd : ∀ cs bs fs numcells st, CodeEntry G tcLevel (cs.length + 1) numcells st →
      n ≤ cs.length + fuel → Comparison G.graph cs bs fs st →
      let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        (cs.length + 1) numcells st).2
      ∃ bs', ReturnCodes G.graph cs bs' fs out ∧
        Grows (State.key G.graph bs st) (State.key G.graph bs' out))
    (cfuel : Nat) (first : Bool) (cs bs fs : List Nat) (numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hl : 1 ≤ cs.length)
    (h : CodeReady G tcLevel cs.length numcells st)
    (ht : Generic.Target State.frame cs.length tc cell st)
    (hv : ∀ v, cursor = some v → cell.mem v = true) (hpast : Generic.Past first tv1 cursor)
    (hrecord : CheapRecorded cs.length tc st) (hroute : RouteRecorded G.graph tcLevel cs.length tc st)
    (hfuel : n ≤ cs.length + fuel) (hcursor : Generic.CursorFuel n cfuel cursor)
    (hc : Comparison G.graph cs bs fs st)
    (hphase : st.compCanon ≤ 0 ∨ first = false ∧ cursor.isSome) :
    let out := (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel cs.length numcells
      tc tv1 cursor cell index st).2.2
    ∃ bs', ReturnCodes G.graph cs bs' fs out ∧
      Grows (State.key G.graph bs st) (State.key G.graph bs' out) := by
  induction cfuel generalizing bs cursor cell index st with
  | zero =>
    cases cursor with
    | none =>
      rw [Generic.sweep]
      have hp : st.compCanon ≤ 0 := by
        rcases hphase with hp | ⟨_, hp⟩
        · exact hp
        · cases hp
      exact ⟨bs, hc.returned hp, Grows.refl _⟩
    | some tv =>
      have hb := hcursor tv rfl
      have hv := VSet.mem_lt (hv tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none =>
      rw [Generic.sweep]
      have hp : st.compCanon ≤ 0 := by
        rcases hphase with hp | ⟨_, hp⟩
        · exact hp
        · cases hp
      exact ⟨bs, hc.returned hp, Grows.refl _⟩
    | some tv =>
      have hmem := hv tv rfl
      have hp : ∀ smaller : VSet n, Generic.Past first tv1 (smaller.nextElem (some tv)) := by
        intro smaller hf v hnext
        have hb := hpast hf tv rfl
        have hn := (VSet.nextElem_eq_some_iff.mp hnext).2.1
        change tv + 1 ≤ v at hn
        omega
      have hf : (first && tv == tv1) = false := by
        cases first with
        | false => rfl
        | true =>
          have hb := hpast rfl tv rfl
          simp only [Bool.true_and, beq_eq_false_iff_ne]
          omega
      let ch := (policy (n := n)).child first cs.length tc tv st
      let raw := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        (cs.length + 1) (numcells + 1) ch
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := (policy (n := n)).recover (n + 2) cs.length left
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
      have hch := h.child hn hl first ht hmem hrecord hroute
      obtain ⟨bs', hr, hg⟩ := hd cs bs fs (numcells + 1) ch hch hfuel (hc.child first cs.length tc tv)
      have hkey : State.key G.graph bs ch = State.key G.graph bs st := by cases first <;> rfl
      rw [hkey] at hg
      have hleft : ReturnCodes G.graph cs bs' fs left := hr.leave tv
      have hback := h.child_return hn hl first fuel ht hmem hrecord hroute
      have hframe := h.ready.child_frame hn hl first ht hmem
        (by simpa only [Nat.add_sub_cancel] using
          node_frame G hn false tcLevel fuel (cs.length + 1) (numcells + 1) ch (by omega) hch.node)
      have hrestore := (h.ready.recover hn hl (hframe.leave tv)).2
      have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
          let out := (next first cs.length numcells tc tv1 (smaller.nextElem (some tv)) smaller index back).2.2
          ∃ ds, ReturnCodes G.graph cs ds fs out ∧
            Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
        intro smaller hs index
        obtain ⟨ds, hr', hg'⟩ := ih bs' index _ smaller back hback.1
          ((ht.subset hs).of_out hrestore.effect) (fun _ hv => VSet.nextElem_mem hv)
          (hp smaller) hback.2.1 hback.2.2 (Generic.CursorFuel.next (hcursor tv rfl))
          (hleft.recover (n + 2)) (Or.inl (recover_nonpos hleft.nonpos (n + 2) cs.length))
        change Grows (State.key G.graph bs' ((policy (n := n)).recover (n + 2) cs.length left)) _ at hg'
        rw [recover_key] at hg'
        exact ⟨ds, hr', hg.trans hg'⟩
      have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
          let out := (Generic.resume (n + 2) next first cs.length numcells tc tv1 tv smaller index left).2.2
          ∃ ds, ReturnCodes G.graph cs ds fs out ∧
            Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
        intro smaller hs
        unfold Generic.resume
        simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
        split
        · exact hcontinue _ (fun _ hv => hs _ (Nauty.longprune_subset hv)) _
        · exact hcontinue smaller hs _
      have hadv :
          let out := (Generic.advance (n + 2) next first cs.length numcells tc tv1 tv cell index left raw.1).2.2
          ∃ ds, ReturnCodes G.graph cs ds fs out ∧
            Grows (State.key G.graph bs st) (State.key G.graph ds out) := by
        cases raw.1 with
        | fuel => exact ⟨bs', hleft, hg⟩
        | done => exact hresume cell (fun _ hv => hv)
        | unwind target short =>
          unfold Generic.advance
          simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
          split
          · exact ⟨bs', hleft, hg⟩
          · split
            · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := left.frame) hv)
            · exact hresume cell (fun _ hv => hv)
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hf, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact hadv
      · rename_i hskip
        have hn : st.compCanon ≤ 0 := by
          rcases hphase with hn | ⟨hf, _⟩
          · exact hn
          · simp only [hf, Bool.not_false, Bool.true_or] at hskip
            exact (hskip trivial).elim
        exact ih bs _ _ cell st h ht (fun _ hv => VSet.nextElem_mem hv) (hp cell) hrecord hroute
          (Generic.CursorFuel.next (hcursor tv rfl)) hc (Or.inl hn)

end Hex.GraphIso.Nauty.Sparse
