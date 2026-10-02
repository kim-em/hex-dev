/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReturnCodes
public import HexGraphIso.Nauty.Sparse.RouteHistory
import all HexGraphIso.Nauty.Sparse.RouteHistory
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

private theorem max_codes_ne {cs bs ds : List Nat} {A B C : Hex.SparseGraph n}
    (hcs : cs ≠ []) (hbs : bs ≠ [])
    (hm : (⟨ds ++ [codeSentinel], C⟩ : Key n) =
      Key.max ⟨bs ++ [codeSentinel], B⟩ ⟨cs ++ [codeSentinel], A⟩) : ds ≠ [] := by
  intro he
  subst ds
  rcases Key.max_mem (⟨bs ++ [codeSentinel], B⟩ : Key n) ⟨cs ++ [codeSentinel], A⟩ with h | h
  · rw [h] at hm
    have hl := congrArg (fun x : Key n => x.codes.length) hm
    simp only [List.length_append, List.length_singleton, List.length_nil] at hl
    exact hbs (List.length_eq_zero_iff.mp (by omega))
  · rw [h] at hm
    have hl := congrArg (fun x : Key n => x.codes.length) hm
    simp only [List.length_append, List.length_singleton, List.length_nil] at hl
    exact hcs (List.length_eq_zero_iff.mp (by omega))

/-- The actual discrete exit returns settled comparisons and the exact
local maximum. First-reference admission obtains its full key from the
retained selected and guided histories, including the terminal sentinel. -/
theorem Comparison.leaf_returned {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {cs bs fs : List Nat} {st : State n} (h : Comparison G.graph cs bs fs st)
    (hh : RouteHistory G.graph tcLevel cs.length cs.length n st)
    (hi : TraceReady G tcLevel cs.length n st) (hn : 0 < n) (hl : 1 ≤ cs.length) :
    let verdict := classify (.ofGraph G.graph) cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs' l c, Label.ofArray? n st.lab = some l ∧ Label.ofArray? n st.canonlab = some c ∧
      ReturnCodes G.graph cs bs' fs out ∧
      State.key G.graph bs' out = some (Key.max ⟨bs ++ [codeSentinel], G.graph.relabel c.perm⟩
        ⟨cs ++ [codeSentinel], G.graph.relabel l.perm⟩) := by
  let verdict := classify (.ofGraph G.graph) cs.length n st
  let out := (leafExit verdict.1 cs.length verdict.2).2
  obtain ⟨l, hlabel⟩ := hi.ready.parse hn
  obtain ⟨f, c, hf, hc, hbound⟩ := h.lower
  obtain ⟨c', hc', hp⟩ := hi.saved.store
  have he : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  have hlen : cs.length ≤ n := Nat.le_trans hi.ready.ok.bc (bcount_le st.ptn cs.length n)
  obtain ⟨bs', d, hd, hmax, hm⟩ := Sparse.leaf_max h.canonical hlen hlabel hc hp (by
    intro ha
    obtain ⟨root, href, hr, route⟩ := hh
    have heq := (classify_first (Prod.ext ha rfl)).2.1
    rw [(route.descent heq).autoFirst_key href hr hi.history h.first (Prod.ext ha rfl)
      hi.saved.work hf hlabel hi.saved.first.2 hi.ready.ok.reach]
    exact hbound)
  have hne := max_codes_ne (by intro he; simp [he] at hl) h.nonempty hmax
  have hr : out.reference = st.reference :=
    (leafExit_reference verdict.1 cs.length verdict.2).trans
      (classify_reference (.ofGraph G.graph) cs.length n st)
  have hfc : out.firstcode = st.firstcode := congrArg Prod.fst hr
  have hfl : out.firstlab = st.firstlab := congrArg (fun r => r.2.2) hr
  have heq : out.eqlevFirst = st.eqlevFirst :=
    (leafExit_eqlev verdict.1 cs.length verdict.2).trans
      (classify_eqlev (.ofGraph G.graph) cs.length n st)
  refine ⟨bs', l, c, hlabel, hc, ?_, ?_⟩
  · refine ⟨⟨cs, ⟨[], List.append_nil _⟩, hm, ?_⟩, hne, f, d, ?_, hd, ?_⟩
    · rw [hfc, heq]
      exact h.first
    · rw [hfl]
      exact hf
    · rw [hmax]
      exact Key.le_trans hbound (Key.le_max_left _ _)
  · change State.key G.graph bs' out = _
    change Label.ofArray? n out.canonlab = some d at hd
    simp only [State.key, hne, ite_false, hd, Option.map_some]
    exact congrArg some hmax

/-- A nonterminal code rejection returns settled machines and leaves
the actual incumbent unchanged. -/
theorem Comparison.prune_returned {G : Hex.SparseGraph n} {numcells : Nat}
    {cs bs fs : List Nat} {st : State n} (h : Comparison G cs bs fs st)
    (hnc : numcells ≠ n) (hbad : (classify (.ofGraph G) cs.length numcells st).1 = .bad) :
    let verdict := classify (.ofGraph G) cs.length numcells st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ReturnCodes G cs bs fs out ∧ State.key G bs out = State.key G bs st := by
  have he : classify (.ofGraph G) cs.length numcells st = (.bad, st) := by
    rw [classify_eq] at hbad ⊢
    split
    · rfl
    · rename_i hnot
      simp only [hnot, bne_iff_ne.mpr hnc, ite_true] at hbad
      contradiction
  have hn : st.compCanon < 0 := by
    rw [classify_eq] at hbad
    split at hbad
    · rename_i hd
      exact (show st.eqlevFirst ≠ cs.length ∧ st.compCanon < 0 by simpa using hd).2
    · simp only [bne_iff_ne.mpr hnc, ite_true] at hbad
      contradiction
  dsimp only
  rw [he]
  have hc : (leafExit .bad cs.length st).2.canonical = st.canonical :=
    leafExit_canonical .bad cs.length st
  refine ⟨(h.returned (by omega)).fields hc
    (leafExit_reference .bad cs.length st) (leafExit_eqlev .bad cs.length st), ?_⟩
  have hcl : (leafExit .bad cs.length st).2.canonlab = st.canonlab :=
    congrArg (fun r => r.2.2.2.2.1) hc
  simp only [State.key, hcl]

/-- Every terminal native classification returns recoverable comparisons
and preserves or increases the incumbent, including internal code rejection. -/
theorem Comparison.exit_returned {G : GraphIso.Sparse.Colored n k} {tcLevel numcells : Nat}
    {cs bs fs : List Nat} {st : State n} (h : Comparison G.graph cs bs fs st)
    (hh : RouteHistory G.graph tcLevel cs.length cs.length numcells st)
    (hi : TraceReady G tcLevel cs.length numcells st) (hn : 0 < n) (hl : 1 ≤ cs.length)
    (hexit : (classify (.ofGraph G.graph) cs.length numcells st).1 ≠ .internal) :
    let verdict := classify (.ofGraph G.graph) cs.length numcells st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs', ReturnCodes G.graph cs bs' fs out ∧
      Grows (State.key G.graph bs st) (State.key G.graph bs' out) := by
  by_cases hnc : numcells = n
  · subst numcells
    obtain ⟨bs', l, c, _, hc, hr, hk⟩ := h.leaf_returned hh hi hn hl
    refine ⟨bs', hr, ?_⟩
    rw [hk]
    simp only [State.key, h.nonempty, ite_false, hc, Option.map_some]
    exact Grows.some (Key.le_max_left _ _)
  · have hbad : (classify (.ofGraph G.graph) cs.length numcells st).1 = .bad := by
      rw [classify_eq] at hexit ⊢
      split
      · rfl
      · rename_i hnot
        simp only [hnot, bne_iff_ne.mpr hnc, ite_true] at hexit
        exact (hexit rfl).elim
    obtain ⟨hr, hk⟩ := h.prune_returned hnc hbad
    exact ⟨bs, hr, hk ▸ Grows.refl _⟩

end Hex.GraphIso.Nauty.Sparse
