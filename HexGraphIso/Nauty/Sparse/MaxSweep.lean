/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxNext
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.ResumeCover
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import HexGraphIso.Nauty.Policy.Generic.MaxExit
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- An exhausted native cursor covers every original selected child,
and its settled code machine identifies the readable incumbent. -/
theorem SweepInput.finished {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {bs fs : List Nat} {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs none cell st parents) :
    Covers (l.node.key G.graph tcLevel) (State.best G.graph st) := by
  have hn : st.compCanon ≤ 0 := by
    rcases h.phase with hn | ⟨_, hf⟩
    · exact hn
    · cases hf
  rw [(h.machine.returned hn).read]
  exact l.cover h.frame h.internal h.selected h.choice (h.cover.finish (fun _ => Remaining.none))

/-- The actual orbit skip preserves the whole traversal context and
advances ranked coverage in the frozen selected cell. -/
theorem SweepInput.skipped {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {bs fs : List Nat} {cell : VSet n} {st : State n} {parents : Parents n} {tv : Nat}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hs : (!l.first || st.orbits[tv]! == tv) = false) :
    SweepInput G tcLevel l bs fs (cell.nextElem (some tv)) cell st parents := by
  have hf : l.first = true := by
    cases he : l.first with
    | true => rfl
    | false => simp only [he, Bool.not_false, Bool.true_or] at hs; cases hs
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have htrace := (h.self hf).freeze h.effect h.selected.ready h.codes.ready hn h.frame.positive
  have hcover := h.cover.skipped h.selected htrace h.orbits h.codes.trace
    (h.subset tv (h.member tv rfl)) hs
  have hnonpos : st.compCanon ≤ 0 := by
    rcases h.phase with hn | ⟨he, _⟩
    · exact hn
    · rw [hf] at he
      cases he
  exact { h with member := fun _ hv => VSet.nextElem_mem hv, cover := hcover, phase := Or.inl hnonpos }

/-- The complete native sibling recursion preserves lower coverage,
including both pruning filters, orbit skips, hinted targets and nonlocal
returns. Only the smaller off-path node result is an induction premise. -/
theorem lower_sweep (G : GraphIso.Sparse.Colored n k) (tcLevel fuel : Nat)
    (hd : NodeMax G tcLevel fuel) (cfuel : Nat) (l : Loop n) (bs fs : List Nat)
    (tv1 index : Nat) (cursor : Option Nat) (cell : VSet n) (st : State n) (parents : Parents n)
    (h : SweepInput G tcLevel l bs fs cursor cell st parents)
    (hfuel : n ≤ l.node.level + fuel) (hcursor : Generic.CursorFuel n cfuel cursor)
    (hpast : Generic.Past l.first tv1 cursor) :
    let out := Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel l.node.level
      (l.cell G.graph tcLevel).numcells (l.cell G.graph tcLevel).tc tv1 cursor cell index st
    ExitCover (l.node.key G.graph tcLevel) (State.best G.graph out.2.2) l.node.level
      (Max.Witness G tcLevel (parents.frames.insert l.node)) out.1 := by
  induction cfuel generalizing bs cursor cell index st with
  | zero =>
    cases cursor with
    | none =>
      rw [Generic.sweep]
      exact h.finished
    | some tv =>
      have hb := hcursor tv rfl
      have hm := VSet.mem_lt (h.member tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none =>
      rw [Generic.sweep]
      exact h.finished
    | some tv =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      let p := l.parent G.graph tcLevel st bs cell tv
      let ch := p.child G.graph tcLevel
      let raw := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := p.back G.graph tcLevel fuel
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st
      let result : Exit × Nat × State n → Prop := fun out =>
        ExitCover (l.node.key G.graph tcLevel) (State.best G.graph out.2.2) l.node.level
          (Max.Witness G tcLevel (parents.frames.insert l.node)) out.1
      have hv := h.member tv rfl
      have hp : p.Valid G tcLevel := h.parent hv
      have hch := h.child rfl
      have hlen : ch.codes.length = l.node.level := by
        change (l.node.codes ++ [_]).length = l.node.level
        simp only [List.length_append, List.length_singleton, h.frame.length]
      have hmax := hd ch bs fs (parents.push p) hch (by rw [hlen]; exact hfuel)
      have hpast' : ∀ smaller : VSet n, Generic.Past l.first tv1 (smaller.nextElem (some tv)) := by
        intro smaller hf v hnext
        have hb := hpast hf tv rfl
        have hn := (VSet.nextElem_eq_some_iff.mp hnext).2.1
        change tv + 1 ≤ v at hn
        omega
      have hfirst : (l.first && tv == tv1) = false := by
        cases he : l.first with
        | false => rfl
        | true =>
          have hb := hpast he tv rfl
          simp only [Bool.true_and, beq_eq_false_iff_ne]
          omega
      have hadv : result (Generic.advance (n + 2) next l.first l.node.level
          (l.cell G.graph tcLevel).numcells (l.cell G.graph tcLevel).tc tv1 tv cell index left raw.1) := by
        cases hx : raw.1 with
        | fuel =>
          unfold Generic.advance
          trivial
        | done =>
          exact (Generic.node_ne_done false (.ofGraph G.graph) (n + 2) tcLevel fuel
            ch.level ch.numcells ch.entry hx).elim
        | unwind target short =>
          have hbound : target ≤ l.node.level := by
            have hh := hmax.coverage
            change ExitCover _ _ l.node.level _ raw.1 at hh
            rw [hx] at hh
            exact hh.1
          by_cases he : target < l.node.level
          · unfold Generic.advance
            simp only [he, ite_true, Id.run_pure]
            have hh := hmax.coverage
            change ExitCover _ _ l.node.level _ raw.1 at hh
            rw [hx] at hh
            have hw : Max.Witness G tcLevel (parents.push p).frames target (State.best G.graph raw.2) := by
              simpa only [ExitCover, ite_eq_right (by omega : target ≠ l.node.level)] using hh.2
            rw [Parents.push_frames hp.node.positive] at hw
            change Max.Witness G tcLevel (parents.frames.insert l.node) target (State.best G.graph left) at hw
            exact ⟨Nat.le_of_lt he, by
              simpa only [ite_eq_right (by omega : target ≠ l.node.level)] using hw⟩
          · have ht : target = l.node.level := by omega
            subst target
            have hcall : raw = (.unwind l.node.level short, raw.2) := by
              rw [← hx]
            have hcovered : Covers (ch.key G.graph tcLevel) (State.best G.graph raw.2) := by
              have hh := hmax.coverage
              change ExitCover _ _ l.node.level _ raw.1 at hh
              rw [hx] at hh
              simpa only [ExitCover, ↓reduceIte] using hh.2
            obtain ⟨ds, hr, resumed⟩ := Scope.receive (p := p) h.scope hp h.codes h.machine h.recorded h.route hfuel
            have hbackRead : State.best G.graph back = State.key G.graph ds back := by
              have hh : State.best G.graph back = State.best G.graph raw.2 :=
                recover_best G.graph (n + 2) l.node.level left
              rw [hh, hr.read]
              exact (recover_key G.graph ds (n + 2) l.node.level left).symm
            have hmax' : MaxResult ((l.cell G.graph tcLevel).child l.first st tv |>.key G.graph tcLevel)
                (State.key G.graph bs ((l.cell G.graph tcLevel).child l.first st tv).entry)
                (State.best G.graph raw.2) l.node.level
                (Max.Witness G tcLevel (parents.push p).frames) (.unwind l.node.level short) := by
              change MaxResult (ch.key G.graph tcLevel) (State.key G.graph bs ch.entry)
                (State.best G.graph raw.2) (ch.level - 1) _ _
              rw [← hx]
              exact hmax
            apply h.cover.advance h.selected h.effect h.pairs h.target hv h.subset
              h.recorded h.counters.2.2 h.capacity
              (l.canon_guide h.selected h.effect h.codes.ready (h.guided tv)) hcall hmax'
            dsimp only
            intro smaller hsub index _ _ hcover
            change (l.cell G.graph tcLevel).Cover G.graph tcLevel
              (Remaining (smaller.nextElem (some tv)) smaller) (State.best G.graph back) at hcover
            rw [hbackRead] at hcover
            exact ih ds index _ smaller back (h.recovered rfl hr resumed hcovered hsub hcover)
              (Generic.CursorFuel.next (hcursor tv rfl)) (hpast' smaller)
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hfirst, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
        apply_ite Prod.fst, apply_ite Prod.snd]
      split
      · exact hadv
      · rename_i hskip
        have hs : (!l.first || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hskip
        exact ih bs _ _ cell st (h.skipped hs)
          (Generic.CursorFuel.next (hcursor tv rfl)) (hpast' cell)

end Hex.GraphIso.Nauty.Sparse.Max
