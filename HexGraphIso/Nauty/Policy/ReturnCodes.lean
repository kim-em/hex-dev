/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Canonical
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

/-- Extending a descent cannot change a code prefix above the extension. -/
theorem prefix_take {cs ds : List Nat} (h : cs <+: ds) {level : Nat}
    (hle : level ≤ cs.length) : ds.take level = cs.take level := by
  obtain ⟨tail, rfl⟩ := h
  exact List.take_append_of_le_length hle

/-- A code-supported witness names the same ancestor after the current
path is truncated, provided the ancestor's child code is retained. -/
theorem prefix_witness {n : Nat} {cs ds : List Nat} {target : Nat} {best : Option (Key n)}
    (hp : cs <+: ds) (ht : target < cs.length)
    (h : ∀ tail : Key n, Generic.Covers (prefixKey (ds.take (target + 1)) tail) best) :
    ∀ tail : Key n, Generic.Covers (prefixKey (cs.take (target + 1)) tail) best := by
  rwa [prefix_take hp (by omega)] at h


variable {n k : Nat}

/-- A completed call retains a settled comparison on an extension of its
incoming code path. The receiving ancestor truncates that extension. -/
structure ReturnCodes (ctx : Ctx n) (stem bs fs : List Nat) (st : Search n) : Prop where
  /-- The last compared path retains every incoming refinement code. -/
  machine : ∃ cs, stem <+: cs ∧ Settled cs bs st ∧ FirstCodes cs fs st
  nonempty : bs ≠ []
  lower : keyLe (incKey ctx fs st.firstlab) (incKey ctx bs st.canonlab)

/-- A stable comparison already supplies a return at its own code path. -/
theorem Comparison.returned {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n}
    (h : Comparison ctx cs bs fs st) (hn : st.compCanon ≤ 0) : ReturnCodes ctx cs bs fs st :=
  ⟨⟨cs, ⟨[], List.append_nil _⟩, .codes h.canonical hn, h.first⟩, h.nonempty, h.lower⟩

/-- The actual discrete leaf action supplies a settled return and its exact local maximum. -/
theorem Comparison.leaf_returned {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {cs bs fs : List Nat} {st : Search n} (h : Comparison ctx cs bs fs st)
    (hh : History ctx tcLevel cs.length cs.length n st) (hinv : RunInv G ctx st)
    (hn0 : 0 < n) (hlevel : 1 ≤ cs.length) (hok : SearchOk G cs.length n st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let verdict := Nauty.classify ctx cs.length n st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ∃ bs', ReturnCodes ctx cs bs' fs out ∧
      out.key ctx bs' = some (incMax (st.key ctx bs) (pathLeafKey ctx cs st.lab)) := by
  obtain ⟨bs', hm, hf, hn, hl, hk⟩ := h.leaf hh hinv hn0 hlevel hok hgsz hsymm hloop
  exact ⟨bs', ⟨⟨cs, ⟨[], List.append_nil _⟩, hm, hf⟩, hn, hl⟩, hk⟩

/-- The actual nonterminal code rejection supplies a settled return and retains its incumbent. -/
theorem Comparison.prune_returned {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n} {numcells : Nat}
    (h : Comparison ctx cs bs fs st) (hnc : numcells ≠ n)
    (hbad : (classify ctx cs.length numcells st).1 = .bad) :
    let verdict := classify ctx cs.length numcells st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    ReturnCodes ctx cs bs fs out ∧ out.key ctx bs = st.key ctx bs := by
  obtain ⟨hm, hf, hk, hl⟩ := h.prune hnc hbad
  exact ⟨⟨⟨cs, ⟨[], List.append_nil _⟩, hm, hf⟩, h.nonempty, hl⟩, hk⟩

/-- Every terminal classification returns settled machines and preserves
or increases the incumbent, including rejection before a discrete leaf. -/
theorem Comparison.exit_returned {G : Colored n k} {ctx : Ctx n} {tcLevel numcells : Nat}
    {cs bs fs : List Nat} {st : Search n} (h : Comparison ctx cs bs fs st)
    (hh : History ctx tcLevel cs.length cs.length numcells st) (hinv : RunInv G ctx st)
    (hn0 : 0 < n) (hlevel : 1 ≤ cs.length) (hok : SearchOk G cs.length numcells st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hexit : (classify ctx cs.length numcells st).1 ≠ .internal) :
    let c := classify ctx cs.length numcells st
    let out := (leafExit c.1 cs.length c.2).2
    ∃ bs', ReturnCodes ctx cs bs' fs out ∧ Generic.Grows (st.key ctx bs) (out.key ctx bs') := by
  by_cases hnc : numcells = n
  · subst numcells
    obtain ⟨bs', hr, hk⟩ := h.leaf_returned hh hinv hn0 hlevel hok hgsz hsymm hloop
    exact ⟨bs', hr, hk ▸ Generic.Grows.incMax _ _⟩
  · have hbad : (classify ctx cs.length numcells st).1 = .bad := by
      rw [classify_eq] at hexit ⊢
      split
      · rfl
      · rename_i hd
        simp only [hd, bne_iff_ne.mpr hnc, ite_true] at hexit
        exact (hexit rfl).elim
    obtain ⟨hr, hk⟩ := h.prune_returned hnc hbad
    exact ⟨bs, hr, hk ▸ Generic.Grows.refl _⟩

/-- A deeper call's code receipt also retains every prefix of its entry path. -/
theorem ReturnCodes.prefix {ctx : Ctx n} {stem cs bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx cs bs fs st) (hp : stem <+: cs) : ReturnCodes ctx stem bs fs st := by
  obtain ⟨ds, hd, hm, hf⟩ := h.machine
  exact ⟨⟨ds, hp.trans hd, hm, hf⟩, h.nonempty, h.lower⟩

/-- Every completed comparison exposes its ghost incumbent in executable storage. -/
theorem ReturnCodes.read {ctx : Ctx n} {stem bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx stem bs fs st) : st.best ctx = st.key ctx bs := by
  obtain ⟨_, _, hm, _⟩ := h.machine
  exact hm.read

/-- Completed comparisons are nonpositive, including a rejection by rows after a code tie. -/
theorem ReturnCodes.nonpos {ctx : Ctx n} {stem bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx stem bs fs st) : st.compCanon ≤ 0 := by
  obtain ⟨_, _, hm, _⟩ := h.machine
  cases hm with
  | codes _ hn => exact hn
  | rows _ hn => omega

/-- Return bookkeeping preserves the complete comparison receipt. -/
theorem ReturnCodes.fields {ctx : Ctx n} {stem bs fs : List Nat} {st out : Search n}
    (h : ReturnCodes ctx stem bs fs st) (hc : out.canonical = st.canonical)
    (hr : out.reference = st.reference) (he : out.eqlevFirst = st.eqlevFirst) :
    ReturnCodes ctx stem bs fs out := by
  obtain ⟨cs, hp, hm, hf⟩ := h.machine
  refine ⟨⟨cs, hp, hm.canonical hc, hf.congr (congrArg Prod.fst hr) he⟩, h.nonempty, ?_⟩
  have hfl : out.firstlab = st.firstlab := congrArg (fun r => r.2.2) hr
  have hcl : out.canonlab = st.canonlab := congrArg (fun r => r.2.2.2.2.1) hc
  rw [hfl, hcl]
  exact h.lower

/-- Removing a temporary fixed point changes no comparison or saved key. -/
theorem ReturnCodes.leave {ctx : Ctx n} {stem bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx stem bs fs st) (tv : Nat) :
    ReturnCodes ctx stem bs fs { st with fixedpts := st.fixedpts.erase tv } :=
  h.fields rfl rfl rfl

/-- Completing a node's symmetry counter preserves its returned comparison. -/
theorem ReturnCodes.afterSweep {ctx : Ctx n} {stem bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx stem bs fs st) (first : Bool) (level size index : Nat) :
    ReturnCodes ctx stem bs fs (Nauty.afterSweep first level size index st) := by
  unfold Nauty.afterSweep
  split <;> exact h.fields rfl rfl rfl

/-- Recovery changes no semantic incumbent labelling. -/
theorem recover_key (ctx : Ctx n) (bs : List Nat) (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).key ctx bs = st.key ctx bs := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals rfl

/-- Finishing a sweep changes no semantic incumbent. -/
theorem afterSweep_key (ctx : Ctx n) (bs : List Nat) (first : Bool)
    (level size index : Nat) (st : Search n) :
    (afterSweep first level size index st).key ctx bs = st.key ctx bs := by
  unfold Nauty.afterSweep
  split <;> rfl

/-- Parent recovery keeps a completed comparison nonpositive. -/
theorem recover_nonpos {st : Search n} (h : st.compCanon ≤ 0) (inf level : Nat) :
    (recoverLevels level (recoverPtn inf level st)).compCanon ≤ 0 := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.compCanon]
  repeat' split
  all_goals first | exact h | omega

/-- Recovery reconstructs both comparison machines at the receiving
ancestor's exact code path, however deep the return originated. -/
theorem ReturnCodes.recover {ctx : Ctx n} {stem bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx stem bs fs st) (inf : Nat) :
    Comparison ctx stem bs fs (recoverLevels stem.length (recoverPtn inf stem.length st)) := by
  obtain ⟨cs, hp, hm, hf⟩ := h.machine
  have hr := comparison_recover hm hf h.nonempty h.lower hp.length_le inf
  have ht : cs.take stem.length = stem := by
    rw [prefix_take hp (Nat.le_refl _), List.take_length]
  rwa [ht] at hr

/-- Recovery supplies a settled receipt at the shortened path for the next sibling. -/
theorem ReturnCodes.resumed {ctx : Ctx n} {stem bs fs : List Nat} {st : Search n}
    (h : ReturnCodes ctx stem bs fs st) (inf : Nat) :
    ReturnCodes ctx stem bs fs (recoverLevels stem.length (recoverPtn inf stem.length st)) :=
  (h.recover inf).returned (recover_nonpos h.nonpos inf stem.length)

end Hex.GraphIso.Nauty
