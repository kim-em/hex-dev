/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.CodeState
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The upper-bound contract of the actual native off-path node at a
fixed recursion bound. Its smaller instance is the node induction premise. -/
def NodeUpper (G : GraphIso.Sparse.Colored n k) (tcLevel fuel : Nat) : Prop :=
  ∀ (f : Frame n) (bs fs : List Nat) (parents : Parents n), f.Valid G →
    CodeEntry G tcLevel f.level f.numcells f.entry → Comparison G.graph f.codes bs fs f.entry →
    Scope G tcLevel f bs f.entry parents → n ≤ f.codes.length + fuel →
    Bounded (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
      (State.best G.graph (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        f.level f.numcells f.entry).2)

/-- The actual native sibling recursion preserves the frozen node's
upper bound. Both filters, skipped vertices, nonlocal exits and recovered
hinted targets are covered; only the smaller node contract is assumed. -/
theorem upper_sweep (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) (tcLevel fuel : Nat)
    (hd : NodeUpper G tcLevel fuel) (cfuel : Nat) (first : Bool) (f : Frame n)
    (bs fs : List Nat) (tc tv1 index : Nat) (cursor : Option Nat) (cell : VSet n) (st : State n)
    (parents : Parents n) (hvalid : f.Valid G)
    (h : CodeReady G tcLevel f.level (f.target G.graph tcLevel).numcells st)
    (hparents : ∀ tv, cell.mem tv = true → (⟨f, first, st, tc, cell, tv, bs⟩ : Parent n).Valid G tcLevel)
    (hs : Scope G tcLevel f bs st parents)
    (hv : ∀ v, cursor = some v → cell.mem v = true) (hpast : Generic.Past first tv1 cursor)
    (hrecord : CheapRecorded f.level tc st) (hroute : RouteRecorded G.graph tcLevel f.level tc st)
    (hfuel : n ≤ f.level + fuel) (hcursor : Generic.CursorFuel n cfuel cursor)
    (hc : Comparison G.graph (f.codes ++ [f.code G.graph]) bs fs st)
    (hphase : st.compCanon ≤ 0 ∨ first = false ∧ cursor.isSome) :
    Bounded (f.key G.graph tcLevel) (State.key G.graph bs st)
      (State.best G.graph (Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
        f.level (f.target G.graph tcLevel).numcells tc tv1 cursor cell index st).2.2) := by
  induction cfuel generalizing bs cursor cell index st with
  | zero =>
    cases cursor with
    | none =>
      have hp : st.compCanon ≤ 0 := by
        rcases hphase with hp | ⟨_, hp⟩
        · exact hp
        · cases hp
      rw [Generic.sweep, (hc.returned hp).read]
      exact Bounded.refl _ _
    | some tv =>
      have hb := hcursor tv rfl
      have hm := VSet.mem_lt (hv tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none =>
      have hp : st.compCanon ≤ 0 := by
        rcases hphase with hp | ⟨_, hp⟩
        · exact hp
        · cases hp
      rw [Generic.sweep, (hc.returned hp).read]
      exact Bounded.refl _ _
    | some tv =>
      have hmem := hv tv rfl
      have hpast' : ∀ smaller : VSet n, Generic.Past first tv1 (smaller.nextElem (some tv)) := by
        intro smaller hf v hnext
        have hb := hpast hf tv rfl
        have hn := (VSet.nextElem_eq_some_iff.mp hnext).2.1
        change tv + 1 ≤ v at hn
        omega
      have hfirst : (first && tv == tv1) = false := by
        cases first with
        | false => rfl
        | true =>
          have hb := hpast rfl tv rfl
          simp only [Bool.true_and, beq_eq_false_iff_ne]
          omega
      let p : Parent n := ⟨f, first, st, tc, cell, tv, bs⟩
      let ch := p.child G.graph tcLevel
      let raw := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := p.back G.graph tcLevel fuel
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
      have hp : p.Valid G tcLevel := hparents tv hmem
      have hch := h.child hn hvalid.positive first hp.target hmem hrecord hroute
      have hlen : ch.codes.length = f.level := by
        change (f.codes ++ [_]).length = f.level
        simp only [List.length_append, List.length_singleton, hvalid.length]
      have hupper := hd ch bs fs (parents.push p) hp.child hch
        (hc.child first f.level tc tv) (hs.push hp) (by rw [hlen]; exact hfuel)
      obtain ⟨ds, hr, resumed⟩ := Scope.receive (p := p) hs hp h hc hrecord hroute hfuel
      have hkey : State.key G.graph bs ch.entry = State.key G.graph bs st := by
        dsimp only [ch, p, Parent.child]
        cases first <;> rfl
      change Bounded (ch.key G.graph tcLevel) (State.key G.graph bs ch.entry) (State.best G.graph raw.2) at hupper
      rw [hr.read, hkey] at hupper
      have hbound : Bounded (f.key G.graph tcLevel) (State.key G.graph bs st) (State.key G.graph ds raw.2) :=
        hupper.absorb hp.child_bound
      have hleft := hr.leave tv
      have hleftBound : Bounded (f.key G.graph tcLevel) (State.key G.graph bs st) (State.best G.graph left) := by
        rw [hleft.read]
        exact hbound
      have hbackBound : Bounded (f.key G.graph tcLevel) (State.key G.graph bs st) (State.key G.graph ds back) := by
        change Bounded _ _ (State.key G.graph ds ((policy (n := n)).recover (n + 2) f.level left))
        rw [recover_key]
        exact hbound
      have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
          Bounded (f.key G.graph tcLevel) (State.key G.graph bs st)
            (State.best G.graph (next first f.level (f.target G.graph tcLevel).numcells tc tv1
              (smaller.nextElem (some tv)) smaller index back).2.2) := by
        intro smaller hsub index
        apply hbackBound.trans
        apply ih ds index _ smaller back resumed.codes
          (fun v hv => resumed.next smaller hsub v hv) resumed.scope
          (fun _ hv => VSet.nextElem_mem hv) (hpast' smaller) resumed.recorded resumed.route
          (Generic.CursorFuel.next (hcursor tv rfl)) resumed.machine
        exact Or.inl (recover_nonpos hleft.nonpos (n + 2) f.level)
      have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
          Bounded (f.key G.graph tcLevel) (State.key G.graph bs st)
            (State.best G.graph (Generic.resume (n + 2) next first f.level (f.target G.graph tcLevel).numcells
              tc tv1 tv smaller index left).2.2) := by
        intro smaller hsub
        unfold Generic.resume
        simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
        split
        · exact hcontinue _ (fun _ hv => hsub _ (Nauty.longprune_subset hv)) _
        · exact hcontinue smaller hsub _
      have hadv : Bounded (f.key G.graph tcLevel) (State.key G.graph bs st)
          (State.best G.graph (Generic.advance (n + 2) next first f.level (f.target G.graph tcLevel).numcells
            tc tv1 tv cell index left raw.1).2.2) := by
        cases raw.1 with
        | fuel => exact hleftBound
        | done => exact hresume cell (fun _ hv => hv)
        | unwind target short =>
          unfold Generic.advance
          simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
          split
          · exact hleftBound
          · split
            · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := left.frame) hv)
            · exact hresume cell (fun _ hv => hv)
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hfirst, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact hadv
      · rename_i hskip
        have hnonpos : st.compCanon ≤ 0 := by
          rcases hphase with hnonpos | ⟨hf, _⟩
          · exact hnonpos
          · simp only [hf, Bool.not_false, Bool.true_or] at hskip
            exact (hskip trivial).elim
        exact ih bs _ _ cell st h hparents hs (fun _ hv => VSet.nextElem_mem hv) (hpast' cell)
          hrecord hroute (Generic.CursorFuel.next (hcursor tv rfl)) hc (Or.inl hnonpos)

end Hex.GraphIso.Nauty.Sparse.Max
