/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceResume
public import HexGraphIso.Nauty.Sparse.Matching
public import HexGraphIso.Nauty.Sparse.Fuel
import HexGraphIso.Nauty.Policy.Generic.MaxExit
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- An actual off-path sweep containing a matching reference returns
emitted evidence above the receiver. The induction follows its finite
cursor, using reference completion only for the actual smaller child calls.
Received returns and both filters retain the original occurrence ledger. -/
theorem SweepInput.reference {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel cfuel boundary tv1 index : Nat} {l : Loop n} {bs fs : List Nat}
    {cursor previous : Option Nat} {cell : VSet n} {st : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents) (hfirst : l.first = false)
    (hbudget : n ≤ l.node.level + fuel) (hcursor : Generic.CursorFuel n cfuel cursor)
    (hboundary : l.node.level < boundary)
    (hvisit : ∀ {tv cell st bs}, SweepInput G tcLevel l bs fs (some tv) cell st parents →
      Generation.Matches G.graph (l.node.level + 1) st targets key →
      st.eqlevFirst = l.node.level → boundary ≤ st.allsamelevel →
      ∀ o, o < (l.cell G.graph tcLevel).len →
      (l.cell G.graph tcLevel).entry.lab[(l.cell G.graph tcLevel).tc + o]! = tv →
      Generation.ChildPath G.graph tcLevel boundary l.node.level
        (State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry)
        (l.cell G.graph tcLevel).tc targets key o →
      let out := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        (l.node.level + 1) ((l.cell G.graph tcLevel).numcells + 1)
        ((policy (n := n)).child l.first l.node.level (l.cell G.graph tcLevel).tc tv st)
      ∀ target short, out.1 = .unwind target short → RefReturn (Graph.context G.graph) target out.2) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    cell.nextElem previous = cursor →
    Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len targets key cell previous →
    (∃ o, o < c.len ∧ Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o) →
    Nauty.Generation.CanonPast l.node.level c.tc previous st →
    Generation.Matches G.graph (l.node.level + 1) st targets key →
    st.eqlevFirst = l.node.level → boundary ≤ st.allsamelevel → l.node.level < st.noncheaplevel →
    let out := Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel l.node.level
      c.numcells c.tc tv1 cursor cell index st
    ∃ target short, out.1 = .unwind target short ∧ target < l.node.level ∧
      RefReturn (Graph.context G.graph) target out.2.2 := by
  intro c R hnext hcover hocc hpast hm heq hsame hcheap
  induction cfuel generalizing bs cursor previous cell index st with
  | zero =>
    cases cursor with
    | none =>
      obtain ⟨o, ho, href⟩ := hocc
      exact (Generation.PathCover.finish hcover hnext o ho href).elim
    | some tv =>
      have := hcursor tv rfl
      have := VSet.mem_lt (h.member tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none =>
      obtain ⟨o, ho, href⟩ := hocc
      exact (Generation.PathCover.finish hcover hnext o ho href).elim
    | some tv =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      let ch := (policy (n := n)).child l.first l.node.level c.tc tv st
      let raw := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
        (l.node.level + 1) (c.numcells + 1) ch
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := (policy (n := n)).recover (n + 2) l.node.level left
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st
      let result : Exit × Nat × State n → Prop := fun out =>
        ∃ target short, out.1 = .unwind target short ∧ target < l.node.level ∧
          RefReturn (Graph.context G.graph) target out.2.2
      have hv := h.member tv rfl
      have hentry := h.codes.child hn h.frame.positive l.first h.target hv h.recorded h.route
      have hsaved : Saved G raw.2 := hentry.saved.node hn tcLevel fuel
        (l.node.level + 1) (c.numcells + 1) (by omega) hentry.node
      have htrace : TraceOk G raw.2 := node_trace G hn tcLevel fuel
        (l.node.level + 1) (c.numcells + 1) ch (by omega) hentry.toTraceEntry
      have hnoncheap : l.node.level < raw.2.noncheaplevel := by
        apply node_noncheap (by omega)
        dsimp only [ch]
        rw [hfirst]
        exact hcheap
      have hsameOut : raw.2.allsamelevel = st.allsamelevel := by
        rw [node_same]
        dsimp only [ch]
        rw [hfirst]
        rfl
      have hadv : result (Generic.advance (n + 2) next l.first l.node.level
          c.numcells c.tc tv1 tv cell index left raw.1) := by
        cases hx : raw.1 with
        | fuel =>
          exact (node_noFuel G hn false tcLevel fuel (l.node.level + 1) (c.numcells + 1) ch
            (by omega) hentry.node (by omega) hx).elim
        | done =>
          exact (Generic.node_ne_done false (.ofGraph G.graph) (n + 2) tcLevel fuel
            (l.node.level + 1) (c.numcells + 1) ch hx).elim
        | unwind target short =>
          by_cases ht : target < l.node.level
          · have hearly := node_early (.ofGraph G.graph) (n + 2) tcLevel fuel
              (l.node.level + 1) (c.numcells + 1) ch hx (by omega)
            have href := hearly.reference hn hsaved htrace ht hnoncheap (by rw [hsameOut]; omega)
            unfold Generic.advance
            simp only [ht, ite_true, Id.run_pure]
            exact ⟨target, short, rfl, ht, href.fixed _⟩
          · have he : target = l.node.level :=
              child_target h.codes.ancestor h.counters.2.2 h.pairs.bound hx (by omega)
            subst target
            have hcall : raw = (.unwind l.node.level short, raw.2) := by rw [← hx]
            let small := if short then (policy (n := n)).shortprune cell left else cell
            let filtered := if !l.first && tv == tv1 then (policy (n := n)).longprune small left else small
            obtain ⟨ds, hresumed⟩ := h.received (tv1 := tv1) hbudget hcall
            change SweepInput G tcLevel l ds fs (filtered.nextElem (some tv)) filtered back parents at hresumed
            have hadvance := h.reference_visit hfirst hcover hpast hnext hcall (fun o ho hat href => by
              have hh := hvisit h hm heq hsame o ho hat href l.node.level short hx
              exact hh)
            have hfiltered := h.reference_filters (tv1 := tv1) hcall hadvance
            change Generation.PathCover G.graph tcLevel boundary l.node.level R c.tc c.len
              targets key filtered (some tv) at hfiltered
            have hpastBack := h.codes.ready.canon_past (tcLevel := tcLevel) (fuel := fuel)
              hn h.frame.positive l.first false h.target hpast hnext
            change Nauty.Generation.CanonPast l.node.level c.tc (some tv) back at hpastBack
            have hreference : back.reference = st.reference := by
              have hb := (referencePolicy (.ofGraph G.graph) (n + 2) tcLevel).recover l.node.level left
              change back.reference = raw.2.reference at hb
              rw [hb, node_reference]
              dsimp only [ch]
              rw [hfirst]
              rfl
            have heqBack : back.eqlevFirst = l.node.level := by
              have he := recover_eqlev (n + 2) l.node.level left
              change back.eqlevFirst = min raw.2.eqlevFirst l.node.level at he
              rw [he]
              apply Nat.min_eq_right
              have hb := Generic.node_bounded (firstFloor (.ofGraph G.graph) (n + 2) tcLevel l.node.level)
                fuel (l.node.level + 1) (c.numcells + 1) ch (by omega)
                (show l.node.level ≤ ch.allsamelevel ∧ l.node.level ≤ ch.eqlevFirst from ?_)
              · exact hb.2
              · dsimp only [ch]
                rw [hfirst]
                change l.node.level ≤ st.allsamelevel ∧ l.node.level ≤ st.eqlevFirst
                exact ⟨by omega, by omega⟩
            have hsameBack : boundary ≤ back.allsamelevel := by
              have he := recover_same (n + 2) l.node.level left
              change back.allsamelevel = raw.2.allsamelevel at he
              rw [he, hsameOut]
              exact hsame
            have hcheapBack : l.node.level < back.noncheaplevel := by
              have he := recover_noncheap (n + 2) l.node.level left
              change back.noncheaplevel =
                (if l.node.level < raw.2.noncheaplevel then l.node.level + 1 else raw.2.noncheaplevel) at he
              rw [he, ite_eq_left hnoncheap]
              omega
            have htail := ih (index := index) hresumed (Generic.CursorFuel.next (hcursor tv rfl)) rfl hfiltered hpastBack
              (hm.congr hreference) heqBack hsameBack hcheapBack
            change result (next l.first l.node.level c.numcells c.tc tv1
              (filtered.nextElem (some tv)) filtered index back) at htail
            unfold Generic.advance Generic.resume
            simp only [Nat.lt_irrefl, ite_false, Id.run_pure, apply_ite Id.run]
            cases hs : short <;> cases ht : tv == tv1
            all_goals simpa only [hfirst, Bool.false_and, Bool.false_eq_true, Bool.not_false,
              Bool.true_and, ite_true, ite_false, small, filtered, back, hs, ht] using htail
      change result (Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel (cfuel + 1)
        l.node.level c.numcells c.tc tv1 (some tv) cell index st)
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hfirst, Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true,
        ite_true, ite_false, Id.run_pure]
      simpa only [raw, ch, left, hfirst] using hadv

end Hex.GraphIso.Nauty.Sparse.Max
