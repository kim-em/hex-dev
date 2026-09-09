/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxTrace
public import HexGraphIso.Nauty.Policy.Coset
import all HexGraphIso.Nauty.Policy.MaxTrace
import all HexGraphIso.Nauty.Policy.MaxStab
import all HexGraphIso.Nauty.Policy.MaxCanon
import all HexGraphIso.Nauty.Policy.MaxAuto
import all HexGraphIso.Nauty.Policy.MaxEmit
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.MaxCarry
import all HexGraphIso.Nauty.Policy.MaxControl
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Coset
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Leaf preparation and action retain the suspended first child's index. -/
theorem Frame.emit_coset (ctx : Ctx n) (tcLevel : Nat) (f : Frame n) :
    (f.emit ctx tcLevel).2.cosetindex = f.entry.cosetindex := by
  unfold Frame.emit
  rw [leafExit_coset, classify_coset]
  dsimp only [prepareOther]
  rw [chooseTarget_fields, compare_coset]
  rfl

/-- A code-two return either names the canonical ancestor or records
that the current coset has acquired a smaller orbit representative. -/
theorem canon_exit (level : Nat) (st : Search n) :
    let out := leafExit .autoCanon level st
    (∃ short, out.1 = .unwind st.gcaCanon short) ∨
      (out.1 = .unwind st.gcaFirst false ∧ out.2.orbits[out.2.cosetindex]! < out.2.cosetindex) := by
  unfold leafExit
  simp only [Id.run_pure, apply_ite Id.run]
  repeat' split
  all_goals simp only [admit_gca, admit_canon]
  all_goals first
    | exact Or.inl ⟨_, rfl⟩
    | exact Or.inr ⟨trivial, by assumption⟩

/-- A smaller orbit representative in a suspended first sweep identifies
an already covered child, using all admitted generators in that frame. -/
theorem Parent.orbit_cover {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} {out : Search n}
    (h : p.Valid G ctx tcLevel) (hgsz : ctx.g.size = n)
    (hi : RunInv G ctx out)
    (hgens : ∀ γ ∈ out.genTrace, CellStab p.state.ptn p.loop.node.level p.state.lab γ)
    (hlt : out.orbits[p.chosen]! < p.chosen)
    (hg : Generic.Grows (p.state.key ctx p.bs) (out.best ctx)) :
    Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) (out.best ctx) := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hok := p.loop.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.node
  have he := h.effect.ptn_eq hok h.partition
  change p.state.ptn = (p.loop.prepare ctx tcLevel).2.2.2.2.ptn at he
  have hv := h.chosen
  have hw := h.effect.window_eq h.cell

  rw [← hw] at hv
  have hchosen : p.chosen < n := VSet.mem_lt h.chosen
  obtain ⟨_, _, w, hword, hend⟩ := (hi.orbits.2 p.chosen hchosen).2
  obtain ⟨ha, hs, hmap⟩ := wordPerm_spec
    (labOk_of_reach hok.labSize hok.reach) hok.ptnSize hok.labSize
    (searchOk_end hn0 hok h.node.positive)
    (fun γ hγ => hi.trace γ (by simpa using hγ))
    (fun γ hγ => by
      have hh := hgens γ (by simpa using hγ)
      rw [he] at hh
      exact LocalAutos.reindexStab hh (cellsPerm_symm h.effect.perm)
        hok.ptnSize h.partition.labSize hok.labSize (searchOk_end hn0 hok h.node.positive))
    w hword
  have hm := windowSet_carry hs h.cell (by rw [hok.labSize]; exact h.range)
    (labOk_of_reach hok.labSize hok.reach) hv
  have hk := hok.vertex_key hn0 h.node.positive hgsz ha hs h.cell h.range hv
    (by have := h.node.depth; omega : p.loop.node.level + 1 + (n - p.loop.node.level) ≤ n + 1) tcLevel
  have hc := h.earlier (wordPerm n w)[p.chosen]! hm (by rw [(hmap p.chosen hchosen).trans hend]; exact hlt)

  rw [p.key h, Loop.key, hk]
  exact hc.grow hg

/-- The actual coset-index exit covers the interrupted first-ancestor
child using the established saved-index and earlier-child invariants. -/
theorem NodeInput.coset_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (he : (f.emit ctx tcLevel).1 = .unwind f.entry.gcaFirst false)
    (hlt : (f.emit ctx tcLevel).2.orbits[(f.emit ctx tcLevel).2.cosetindex]! <
      (f.emit ctx tcLevel).2.cosetindex)
    {p : Parent n} (hp : parents f.entry.gcaFirst = some p)
    (hg : Generic.Grows (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)) :
    Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) ((f.emit ctx tcLevel).2.best ctx) := by
  obtain ⟨_, _, hlevel, hv⟩ := h.scope.valid _ p hp
  have href := h.scope.coset _ p hp (comparison_positive h.entry.2) rfl
  have hkeep := h.emit_keeps hgsz hsymm hloop
  rw [he] at hkeep
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hi : RunInv G ctx (f.emit ctx tcLevel).2 :=
    (h.entry.1.prepare hn0 hgsz hsymm hloop).2.2.2.1
  apply Parent.orbit_cover hv hgsz hi
  · intro γ hγ
    rw [hlevel]
    exact hkeep _ p hp href.1 (Nat.le_refl _) γ hγ
  · rwa [f.emit_coset, href.2] at hlt
  · exact (h.scope.grows _ p hp).trans hg

/-- Every actual code-two return satisfies the maximum rule, including
the early return selected by a smaller coset representative. -/
theorem auto_canon (G : Colored n k) (tcLevel : Nat) :
    NodeRule G tcLevel false (fun level numcells st => verdict G tcLevel level numcells st = .autoCanon) := by
  intro fuel _ level numcells st ha cs bs fs parents h
  let ctx : Ctx n := { g := rowsOf G }
  let f : Frame n := ⟨level, numcells, cs, st⟩
  let prep := prepareOther ctx tcLevel level numcells st
  let c := classify ctx level prep.1 prep.2.2.2.2.2
  have hclass : c.1 = .autoCanon := ha
  have hdone : (f.emit ctx tcLevel).1 ≠ .done := by
    intro he
    have hh := (leafExit_done c.1 level c.2).mp he
    rw [hclass] at hh
    cases hh
  rw [f.emit_step _ hdone]
  have hx := canon_exit level c.2
  rw [← hclass] at hx
  change (∃ short, (f.emit ctx tcLevel).1 = .unwind c.2.gcaCanon short) ∨
    ((f.emit ctx tcLevel).1 = .unwind c.2.gcaFirst false ∧
      (f.emit ctx tcLevel).2.orbits[(f.emit ctx tcLevel).2.cosetindex]! <
        (f.emit ctx tcLevel).2.cosetindex) at hx
  have hgf : c.2.gcaFirst = st.gcaFirst :=
    (leafExit_gca c.1 level c.2).symm.trans (f.emit_first ctx tcLevel).2
  have hgc : c.2.gcaCanon = st.gcaCanon := by
    have hh : (leafExit c.1 level c.2).2.gcaCanon = c.2.gcaCanon := by rw [hclass, autoCanon_ancestor]
    exact hh.symm.trans (f.emit_canon ha).2
  rw [hgf, hgc] at hx
  rcases hx with ⟨short, he⟩ | ⟨he, hlt⟩
  · exact h.canon_return (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) ha he
  · have hb := h.leaf_best (canon_discrete ha) (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
    change (f.emit ctx tcLevel).2.best ctx = some (incMax (st.key ctx bs) (f.key ctx tcLevel)) at hb
    have hg : Generic.Grows (st.key ctx bs) ((f.emit ctx tcLevel).2.best ctx) := by
      rw [hb]; exact Generic.Grows.incMax _ _
    refine ⟨Generic.Bounded.of_eq hb, ?_⟩
    rw [he]
    have ht : st.gcaFirst < level := h.entry.1.ancestor
    refine ⟨by omega, ?_⟩
    split
    · rw [hb]; exact Generic.Covers.incMax _ _
    · have hp := (h.counters (comparison_positive h.entry.2)).1
      obtain ⟨p, hp⟩ := h.scope.complete st.gcaFirst hp ht
      obtain ⟨_, _, hlevel, hv⟩ := h.scope.valid st.gcaFirst p hp
      have hc := h.coset_cover (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) he hlt hp hg
      refine ⟨p.child ctx tcLevel, ?_, ?_, Or.inl hc⟩
      · simp only [Parents.frames, show st.gcaFirst ≠ 0 by omega, ↓reduceIte, hp, Option.map_some, ctx]
      · change p.loop.node.level + 1 ≤ n
        have hd : level ≤ n := h.frame.depth
        omega

end Hex.GraphIso.Nauty.Max
