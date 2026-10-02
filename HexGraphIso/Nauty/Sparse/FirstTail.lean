/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceDescent
public import HexGraphIso.Nauty.Sparse.MaxSweep
public import HexGraphIso.Nauty.Sparse.MaxNode
public import HexGraphIso.Nauty.Sparse.Fuel
public import HexGraphIso.Nauty.Sparse.EarlyReturn
public import HexGraphIso.Nauty.Sparse.ReferenceReturn
import HexGraphIso.Nauty.Policy.Generic.MaxExit
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.ResumeCover
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Sparse.CheapHistory
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Every remaining child of a cheap first-path receiver reaches the
saved reference and returns to this receiver. Its history is supplied by
the actual sweep invariants after all preceding sibling searches. -/
theorem SweepInput.cheap_visit {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel : Nat} {l : Loop n} {bs fs : List Nat} {tv : Nat}
    {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hf : l.first = true) (heq : st.eqlevFirst = l.node.level)
    (hcheap : st.noncheaplevel ≤ l.node.level) (hbudget : n ≤ l.node.level + fuel) :
    (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) ((l.cell G.graph tcLevel).numcells + 1)
      ((policy (n := n)).child l.first l.node.level (l.cell G.graph tcLevel).tc tv st)).1 =
        .unwind l.node.level false := by
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hg := h.first hf
  have hc : st.noncheaplevel ≤ st.gcaFirst := by omega
  obtain ⟨root, href, hd, hr, hshape, ha⟩ := h.codes.history hc
  obtain ⟨f, hlabel⟩ := Label.ofArray?_exists
    (isPerm_of_cellsReach h.codes.saved.first.1 hn h.codes.saved.first.2)
  have hdepth : l.node.level ≤ href.last := by have := hd.1; omega
  have hnc : (l.cell G.graph tcLevel).numcells < n := h.internal
  have hresult := (ha.descent heq).child_returns href hdepth hr hshape h.codes.ready hn
    h.frame.positive hnc h.target (h.member tv rfl) (h.recorded hc heq)
    h.codes.saved.work hlabel h.codes.saved.first.2 heq (Nat.le_of_eq hg) l.first
    (n + 2) fuel (by omega)
  exact hresult.1.trans (by rw [hg])

/-- Every later first-path child returns to its immediate receiver.
Cheap receivers use the emitted reference; other receivers use the
proved bounds of the actual return, including short pruning returns. -/
theorem SweepInput.visit_level {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel target : Nat} {short : Bool} {l : Loop n} {bs fs : List Nat} {tv : Nat}
    {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hf : l.first = true) (heq : st.eqlevFirst = l.node.level)
    (hsame : l.node.level < st.allsamelevel) (hbudget : n ≤ l.node.level + fuel)
    (he : (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) ((l.cell G.graph tcLevel).numcells + 1)
      ((policy (n := n)).child l.first l.node.level (l.cell G.graph tcLevel).tc tv st)).1 =
        .unwind target short) : target = l.node.level := by
  by_cases hc : st.noncheaplevel ≤ l.node.level
  · have hr := h.cheap_visit hf heq hc hbudget
    rw [he] at hr
    cases hr
    rfl
  · have hg := h.first hf
    have hfloor : l.node.level ≤ target := by
      apply node_floor (by omega) _ _ _ _ he
      · rw [hf]; exact Nat.le_of_eq hg.symm
      · rw [hf]; exact Nat.le_trans (Nat.le_of_eq hg.symm) h.counters.2.1
      · rw [hf]; exact Nat.lt_of_not_ge hc
      · rw [hf]; exact hsame
    exact child_target (Nat.le_of_eq hg) h.counters.2.2 h.pairs.bound he hfloor

/-- A later first-path child returns normally, with no short-prune
request. Sufficient fuel and the positive first ancestor exclude every
other executed exit. -/
theorem SweepInput.visit_return {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel : Nat} {l : Loop n} {bs fs : List Nat} {tv : Nat}
    {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hf : l.first = true) (heq : st.eqlevFirst = l.node.level)
    (hsame : l.node.level < st.allsamelevel) (hbudget : n ≤ l.node.level + fuel) :
    (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) ((l.cell G.graph tcLevel).numcells + 1)
      ((policy (n := n)).child l.first l.node.level (l.cell G.graph tcLevel).tc tv st)).1 =
        .unwind l.node.level false := by
  let ch := (policy (n := n)).child l.first l.node.level (l.cell G.graph tcLevel).tc tv st
  let out := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
    (l.node.level + 1) ((l.cell G.graph tcLevel).numcells + 1) ch
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hch := h.codes.ready.child hn h.frame.positive l.first h.target (h.member tv rfl)
  change out.1 = _
  cases hx : out.1 with
  | fuel =>
    exact (node_noFuel G hn false tcLevel fuel (l.node.level + 1)
      ((l.cell G.graph tcLevel).numcells + 1) ch (by omega) hch (by omega) hx).elim
  | done =>
    exact (Generic.node_ne_done false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (l.node.level + 1) ((l.cell G.graph tcLevel).numcells + 1) ch hx).elim
  | unwind target short =>
    have ht := h.visit_level hf heq hsame hbudget hx
    subst target
    cases short with
    | false => rfl
    | true =>
      have hshort := node_short_first h.frame.positive hx
      have hg : ch.gcaFirst = l.node.level := by
        dsimp only [ch]
        rw [hf]
        exact h.first hf
      exact (hshort hg.symm).elim

/-- The complete remaining first-path sweep finishes. Every surviving
child returns locally, and recovery retains the first-code and all-same
bounds through both native pruning filters and orbit skips. -/
theorem SweepInput.tail_done {G : GraphIso.Sparse.Colored n k} {tcLevel fuel cfuel : Nat}
    {l : Loop n} {bs fs : List Nat} {tv1 index : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents)
    (hf : l.first = true) (heq : st.eqlevFirst = l.node.level)
    (hsame : l.node.level < st.allsamelevel) (hbudget : n ≤ l.node.level + fuel)
    (hcursor : Generic.CursorFuel n cfuel cursor) (hpast : Generic.Past l.first tv1 cursor) :
    (Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel l.node.level
      (l.cell G.graph tcLevel).numcells (l.cell G.graph tcLevel).tc tv1 cursor cell index st).1 = .done := by
  induction cfuel generalizing bs cursor cell index st with
  | zero =>
    cases cursor with
    | none => rw [Generic.sweep]
    | some tv =>
      have := hcursor tv rfl
      have := VSet.mem_lt (h.member tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none => rw [Generic.sweep]
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
      let result : Exit × Nat × State n → Prop := fun out => out.1 = .done
      have hv := h.member tv rfl
      have hp : p.Valid G tcLevel := h.parent hv
      have hch := h.child rfl
      have hlen : ch.codes.length = l.node.level := by
        change (l.node.codes ++ [_]).length = l.node.level
        simp only [List.length_append, List.length_singleton, h.frame.length]
      have hmax := node_max G tcLevel fuel ch bs fs (parents.push p) hch (by rw [hlen]; exact hbudget)
      have hpast' : ∀ smaller : VSet n, Generic.Past l.first tv1 (smaller.nextElem (some tv)) := by
        intro smaller _ v hnext
        have := hpast hf tv rfl
        have hh := (VSet.nextElem_eq_some_iff.mp hnext).2.1
        change tv + 1 ≤ v at hh
        omega
      have hfirst : (l.first && tv == tv1) = false := by
        have := hpast hf tv rfl
        simp only [hf, Bool.true_and, beq_eq_false_iff_ne]
        omega
      have heqBack : back.eqlevFirst = l.node.level := by
        have he := recover_eqlev (n + 2) l.node.level left
        change back.eqlevFirst = min raw.2.eqlevFirst l.node.level at he
        rw [he]
        apply Nat.min_eq_right
        have hb := Generic.node_bounded (firstFloor (.ofGraph G.graph) (n + 2) tcLevel l.node.level)
          fuel ch.level ch.numcells ch.entry (by change l.node.level < l.node.level + 1; omega)
          (show l.node.level ≤ ch.entry.allsamelevel ∧ l.node.level ≤ ch.entry.eqlevFirst from ?_)
        · exact hb.2
        · dsimp only [ch, p, Parent.child, Loop.parent]
          rw [hf]
          exact ⟨Nat.le_of_lt hsame, Nat.le_of_eq heq.symm⟩
      have hsameBack : l.node.level < back.allsamelevel := by
        have he := recover_same (n + 2) l.node.level left
        change back.allsamelevel = raw.2.allsamelevel at he
        rw [he, node_same]
        dsimp only [ch, p, Parent.child, Loop.parent]
        rw [hf]
        exact hsame
      have hadv : result (Generic.advance (n + 2) next l.first l.node.level
          (l.cell G.graph tcLevel).numcells (l.cell G.graph tcLevel).tc tv1 tv cell index left raw.1) := by
        cases hx : raw.1 with
        | fuel =>
          exact (node_noFuel G hn false tcLevel fuel ch.level ch.numcells ch.entry
            hch.frame.positive hch.frame.node (by change n + 1 ≤ l.node.level + 1 + fuel; omega) hx).elim
        | done =>
          exact (Generic.node_ne_done false (.ofGraph G.graph) (n + 2) tcLevel fuel
            ch.level ch.numcells ch.entry hx).elim
        | unwind target short =>
          have ht : target = l.node.level := h.visit_level hf heq hsame hbudget hx
          subst target
          have hcall : raw = (.unwind l.node.level short, raw.2) := by rw [← hx]
          have hcovered : Covers (ch.key G.graph tcLevel) (State.best G.graph raw.2) := by
            have hh := hmax.coverage
            change ExitCover _ _ l.node.level _ raw.1 at hh
            rw [hx] at hh
            simpa only [ExitCover, ↓reduceIte] using hh.2
          obtain ⟨ds, hr, resumed⟩ := Scope.receive (p := p) h.scope hp h.codes h.machine
            h.recorded h.route hbudget
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
          exact ih (h.recovered rfl hr resumed hcovered hsub hcover) heqBack hsameBack
            (Generic.CursorFuel.next (hcursor tv rfl)) (hpast' smaller)
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hfirst, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
        apply_ite Prod.fst]
      split
      · exact hadv
      · rename_i hskip
        have hs : (!l.first || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hskip
        exact ih (h.skipped hs) heq hsame
          (Generic.CursorFuel.next (hcursor tv rfl)) (hpast' cell)

end Hex.GraphIso.Nauty.Sparse.Max
