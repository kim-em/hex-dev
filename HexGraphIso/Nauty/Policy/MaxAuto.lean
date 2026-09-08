/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxEmit
public import HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxEmit
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxLeaf
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.CanonScatter
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- A scatter from a covered reference child covers the entire chosen
child of the frozen parent, independently of the emitting leaf's depth. -/
theorem Parent.scatter_cover {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel) {ref lab γ : Array Nat}
    {best : Option (Key n)}
    (hgsz : ctx.g.size = n) (href : ref.size = n)
    (hcheck : checkAutom ctx.g γ = true)
    (hfr : cellsPerm (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
      (p.loop.prepare ctx tcLevel).2.2.2.2.lab ref)
    (hl : cellsPerm (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
      (p.loop.prepare ctx tcLevel).2.2.2.2.lab lab)
    (hmap : ∀ i, i < n → γ[ref[i]!]! = lab[i]!)
    (hchosen : lab[(p.loop.prepare ctx tcLevel).2.1.toNat]! = p.chosen)
    (hcover : Generic.Covers (p.loop.key ctx tcLevel ref[(p.loop.prepare ctx tcLevel).2.1.toNat]!) best) :
    Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) best := by
  let base := (p.loop.prepare ctx tcLevel).2.2.2.2
  let tc := (p.loop.prepare ctx tcLevel).2.1.toNat
  let len := (p.loop.prepare ctx tcLevel).2.2.2.1
  have hok := p.loop.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.node
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hs := cellStab_of_scatter hok.ptnSize hok.labSize href
    (searchOk_end hn0 hok h.node.positive) hfr hl hmap
  have hmem : (windowSet n base.lab tc len).mem ref[tc]! = true := by
    have hm : ref[tc]! ∈ segN base.lab tc len := by
      exact (hfr tc len h.cell).mem_iff.mpr (mem_segN_iff.mpr ⟨0, h.cell.1, by simp⟩)
    apply mem_windowSet.mpr
    refine ⟨?_, hm⟩
    obtain ⟨o, ho, he⟩ := mem_segN_iff.mp hm
    rw [← he]
    exact (labOk_of_reach hok.labSize hok.reach) _ (by
      have hsz : base.lab.size = n := hok.labSize
      change tc + o < base.lab.size
      have hr : tc + len ≤ n := h.range
      omega)
  have hat : γ[ref[tc]!]! = p.chosen :=
    (hmap tc (by have := h.range; have := h.len; omega)).trans hchosen
  have hk := hok.vertex_key hn0 h.node.positive hgsz hcheck hs h.cell h.range hmem
    (by have := h.node.depth; omega : p.loop.node.level + 1 + (n - p.loop.node.level) ≤ n + 1) tcLevel
  rw [hat] at hk
  dsimp only [Search.view] at hk
  rw [p.key h, Loop.key, ← hk]
  exact hcover

/-- The actual leaf action has the same ancestor partition effect as a
node call, whether or not it changes the incumbent. -/
theorem NodeInput.emit_out {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents) :
    SearchOut G (f.level - 1) f.level f.entry.view (f.emit ctx tcLevel).2.view := by
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  let rp := reachPolicy G ctx tcLevel hn0
  have hv := rp.visit f.level f.numcells f.entry h.frame.positive h.frame.partition
  have hc := rp.compare f.level (visit ctx f.level f.numcells f.entry).2.1 _ _ hv.1
  have ht := rp.target false f.level _ _ h.frame.positive hc.ok
  exact hv.2 _ (hc.effect.trans (ht.1.effect.trans (leaf_out ht.1.ok)))

/-- A saved ancestor's chosen vertex is retained at every actual emitter. -/
theorem NodeInput.emit_chosen {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    {t : Nat} {p : Parent n} (hp : parents t = some p) :
    (f.emit ctx tcLevel).2.lab[(p.loop.prepare ctx tcLevel).2.1.toNat]! = p.chosen :=
  (h.emit_out.atSingleton (h.singletons hp)).trans (h.scope.chosen t p hp)

/-- The emitting leaf remains within every saved ancestor's cells. -/
theorem NodeInput.emit_parent {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    {t : Nat} {p : Parent n} (hp : parents t = some p) :
    cellsPerm (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
      (p.loop.prepare ctx tcLevel).2.2.2.2.lab (f.emit ctx tcLevel).2.lab := by
  obtain ⟨ht, htl, he, hv⟩ := h.scope.valid t p hp
  have hok := hv.partition
  rw [he] at hok
  have ho := extend_refinement ht htl hok h.frame.partition (h.scope.effect t p hp) h.emit_out
  rw [← he] at ho
  have hperm := cellsPerm_trans hv.effect.perm (by
    intro a len hc
    exact ho.perm a len (isCell_of_low hv.effect.low hc))
  exact hperm

/-- Leaf processing retains the first reference and its ancestor. -/
theorem Frame.emit_first (ctx : Ctx n) (tcLevel : Nat) (f : Frame n) :
    (f.emit ctx tcLevel).2.firstlab = f.entry.firstlab ∧
      (f.emit ctx tcLevel).2.gcaFirst = f.entry.gcaFirst := by
  unfold Frame.emit
  have hclass : ∀ nc (st : Search n), (classify ctx f.level nc st).2.gcaFirst = st.gcaFirst :=
    (gcaPolicy ctx 0 tcLevel).classify f.level
  rw [(leafExit_frame ..).2.2.1, (classify_frame ..).2.2.1, leafExit_gca, hclass]
  dsimp only [prepareOther]
  rw [chooseTarget_fields]
  constructor
  · exact (compareCodes_frame ..).2.2.1
  · exact (gcaPolicy ctx 0 tcLevel).compare _ _ _

/-- The actual first-reference verdict supplies its checked scatter,
expressed entirely in the emitting state's fields. -/
theorem NodeInput.first_scatter {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoFirst) :
    let out := (f.emit ctx tcLevel).2
    checkAutom ctx.g out.workperm = true ∧ out.firstlab.size = n ∧
      ∀ i, i < n → out.workperm[out.firstlab[i]!]! = out.lab[i]! := by
  intro out
  let p := prepareOther ctx tcLevel f.level f.numcells f.entry
  let c := classify ctx f.level p.1 p.2.2.2.2.2
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  obtain ⟨hok, hi, hh, _, _⟩ := h.entry.1.prepare hn0 hgsz hsymm hloop
  have hc : c.1 = .autoFirst := hauto
  have hchecked := hh.checked hi hn0 hok hgsz hsymm hloop (Or.inl hc)
  have hclass : classify ctx f.level p.1 p.2.2.2.2.2 = (.autoFirst, c.2) := Prod.ext hc rfl
  obtain ⟨_, _, hscatter, _⟩ := classify_first hclass
  have hw : out.workperm = c.2.workperm := leafExit_workperm c.1 f.level c.2
  have hf : out.firstlab = p.2.2.2.2.2.firstlab :=
    (leafExit_frame c.1 f.level c.2).2.2.1.trans (classify_frame ctx f.level p.1 _).2.2.1
  have hl : out.lab = p.2.2.2.2.2.lab :=
    (leafExit_frame c.1 f.level c.2).1.trans (classify_frame ctx f.level p.1 _).1
  refine ⟨hw ▸ hchecked, hf ▸ hi.firstSize, ?_⟩
  intro i hiN
  rw [hw, hf, hl, hscatter]
  exact scatter_map hi.scratch hi.firstSize hi.first i hiN

/-- A positive first-ancestor return covers that ancestor's entire chosen
child from its saved first-reference coverage. -/
theorem NodeInput.first_cover {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoFirst)
    {t : Nat} {p : Parent n} (hp : parents t = some p) (ht : f.entry.gcaFirst = t)
    (hg : Generic.Grows (f.entry.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)) :
    Generic.Covers ((p.child ctx tcLevel).key ctx tcLevel) ((f.emit ctx tcLevel).2.best ctx) := by
  obtain ⟨_, _, he, hv⟩ := h.scope.valid t p hp
  have hf := h.scope.first t p hp (by omega)
  have hparent : p.state.gcaFirst = p.loop.node.level := hf.1.symm.trans (ht.trans he.symm)
  obtain ⟨hc, hr⟩ := hv.first hparent
  have hfields := f.emit_first ctx tcLevel
  have href : (f.emit ctx tcLevel).2.firstlab = p.state.firstlab := hfields.1.trans hf.2
  have hsc := h.first_scatter hgsz hsymm hloop hauto
  apply Parent.scatter_cover hv hgsz hsc.2.1 hsc.1
  · rw [href]; exact hr
  · exact h.emit_parent hp
  · exact hsc.2.2
  · exact h.emit_chosen hp
  · rw [href]
    exact hc.grow ((h.scope.grows t p hp).trans hg)

/-- Code one returns to the first ancestor without requesting a short prune. -/
theorem first_exit (level : Nat) (st : Search n) :
    (leafExit .autoFirst level st).1 =
      .unwind (leafExit .autoFirst level st).2.gcaFirst false := by
  unfold leafExit
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd]
  split <;> rfl

/-- The actual first-reference emission satisfies its entire maximum
rule, including returns across arbitrarily many intermediate sweeps. -/
theorem auto_first (G : Colored n k) (tcLevel : Nat) :
    NodeRule G tcLevel false (fun level numcells st => verdict G tcLevel level numcells st = .autoFirst) := by
  intro fuel _ level numcells st ha cs bs fs parents h
  let ctx : Ctx n := { g := rowsOf G }
  let f : Frame n := ⟨level, numcells, cs, st⟩
  let p := prepareOther ctx tcLevel level numcells st
  let c := classify ctx level p.1 p.2.2.2.2.2
  have hclass : c.1 = .autoFirst := ha
  have hd : p.1 = n := (classify_first (Prod.ext hclass rfl)).1
  have he : (f.emit ctx tcLevel).1 = .unwind st.gcaFirst false := by
    have hx := first_exit level c.2
    rw [← hclass] at hx
    change (f.emit ctx tcLevel).1 = .unwind (f.emit ctx tcLevel).2.gcaFirst false at hx
    rwa [(f.emit_first ctx tcLevel).2] at hx
  have hdone : (f.emit ctx tcLevel).1 ≠ .done := by rw [he]; intro h; cases h
  have hb := h.leaf_best hd (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
  change (f.emit ctx tcLevel).2.best ctx = some (incMax (st.key ctx bs) (f.key ctx tcLevel)) at hb
  have hg : Generic.Grows (st.key ctx bs) ((f.emit ctx tcLevel).2.best ctx) := by
    rw [hb]; exact Generic.Grows.incMax _ _
  have hr : Generic.Result (f.key ctx tcLevel) (st.key ctx bs) ((f.emit ctx tcLevel).2.best ctx)
      (level - 1) (Witness ctx tcLevel (parents.frames ctx tcLevel)) (f.emit ctx tcLevel).1 := by
    refine ⟨Generic.Bounded.of_eq hb, ?_⟩
    rw [he]
    have hlt : st.gcaFirst < level := h.entry.1.ancestor
    refine ⟨by omega, ?_⟩
    split
    · rw [hb]; exact Generic.Covers.incMax _ _
    · rename_i hne
      have hpos := (h.counters (comparison_positive h.entry.2)).1
      obtain ⟨q, hq⟩ := h.scope.complete st.gcaFirst hpos hlt
      obtain ⟨_, _, hlevel, hv⟩ := h.scope.valid st.gcaFirst q hq
      have hcover := h.first_cover (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) ha hq rfl hg
      refine ⟨q.child ctx tcLevel, ?_, ?_, Or.inl hcover⟩
      · simp only [Parents.frames, show st.gcaFirst ≠ 0 by omega, ↓reduceIte, hq, Option.map_some]
      · change q.loop.node.level + 1 ≤ n
        have hd : level ≤ n := h.frame.depth
        omega
  rw [f.emit_step _ hdone]
  exact hr

end Hex.GraphIso.Nauty.Engine.Max
