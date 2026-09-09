/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Canon
import all HexGraphIso.Nauty.Policy.Max.Canon
import all HexGraphIso.Nauty.Policy.Max.Auto
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Prepare
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Invariant.PathStab
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A permutation stabilizing a saved target frame stabilizes every
coarser saved ancestor. Their effects into the same current state supply
both the cell-content transport and the boundary inclusion. -/
theorem Scope.stab_below {G : Colored n k} {ctx : Ctx n} {tcLevel level : Nat}
    {cs bs : List Nat} {st : Search n} {parents : Parents n}
    (h : Scope G ctx tcLevel level cs bs st parents)
    {a b : Nat} {p q : Parent n} {γ : Array Nat}
    (hp : parents a = some p) (hq : parents b = some q) (hab : a ≤ b)
    (hs : CellStab q.state.ptn b q.state.lab γ) :
    CellStab p.state.ptn a p.state.lab γ := by
  obtain ⟨ha, _, hpa, hpv⟩ := h.valid a p hp
  obtain ⟨hb, _, hqb, hqv⟩ := h.valid b q hq
  have hpk := hpv.partition
  have hqk := hqv.partition
  rw [hpa] at hpk
  rw [hqb] at hqk
  have hn0 : 0 < n := by have := hpv.node.positive; have := hpv.node.depth; omega
  have hpe := h.effect a p hp
  have hqe := h.effect b q hq
  have hsz : st.lab.size = n := hqe.labSize.trans hqk.labSize
  have hepa := searchOk_end hn0 hpk ha
  have heqb := searchOk_end hn0 hqk hb
  have hr := LocalAutos.reindexStab hs hqe.perm hqk.ptnSize hqk.labSize hsz heqb
  have hc : CellStab p.state.ptn a st.lab γ := by
    apply cellsPerm_coarsen (ptnF := q.state.ptn) (levF := b)
      (hpk.ptnSize.trans hqk.ptnSize.symm) (hsz.trans hqk.ptnSize.symm)
      (by rw [Array.size_map]; exact hsz.trans hqk.ptnSize.symm) hr heqb hepa
    intro i hi
    change p.state.ptn[i]! ≤ a at hi
    change q.state.ptn[i]! ≤ b
    have he := hpe.low i (Or.inl hi)
    change st.ptn[i]! = p.state.ptn[i]! at he
    have heq := hqe.low i (Or.inr (by change st.ptn[i]! ≤ b; omega))
    change st.ptn[i]! = q.state.ptn[i]! at heq
    omega
  exact LocalAutos.reindexStab hc (cellsPerm_symm hpe.perm)
    hpk.ptnSize hsz hpk.labSize hepa

/-- The actual target-frame ordering has the same stabilization relation
as the frozen sweep ordering. -/
theorem Parent.reindex_stab {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel) {γ : Array Nat}
    (hs : CellStab (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
      (p.loop.prepare ctx tcLevel).2.2.2.2.lab γ) :
    CellStab p.state.ptn p.loop.node.level p.state.lab γ := by
  have hok := p.loop.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.node
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hp := h.effect.ptn_eq hok h.partition
  change p.state.ptn = (p.loop.prepare ctx tcLevel).2.2.2.2.ptn at hp
  rw [hp]
  exact LocalAutos.reindexStab hs h.effect.perm hok.ptnSize hok.labSize h.partition.labSize
    (searchOk_end hn0 hok h.node.positive)

/-- A reference scatter stabilizes the actual saved parent partition. -/
theorem Parent.scatter_stab {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel) {ref lab γ : Array Nat}
    (href : ref.size = n)
    (hfr : cellsPerm (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
      (p.loop.prepare ctx tcLevel).2.2.2.2.lab ref)
    (hl : cellsPerm (p.loop.prepare ctx tcLevel).2.2.2.2.ptn p.loop.node.level
      (p.loop.prepare ctx tcLevel).2.2.2.2.lab lab)
    (hmap : ∀ i, i < n → γ[ref[i]!]! = lab[i]!) :
    CellStab p.state.ptn p.loop.node.level p.state.lab γ := by
  have hok := p.loop.prepare_ok (ctx := ctx) (tcLevel := tcLevel) h.node
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  exact Parent.reindex_stab h (cellStab_of_scatter hok.ptnSize hok.labSize href
    (searchOk_end hn0 hok h.node.positive) hfr hl hmap)

/-- Code one's scatter stabilizes its saved first ancestor. -/
theorem NodeInput.first_stab {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoFirst)
    {p : Parent n} (hp : parents f.entry.gcaFirst = some p) :
    CellStab p.state.ptn f.entry.gcaFirst p.state.lab (f.emit ctx tcLevel).2.workperm := by
  obtain ⟨_, _, he, hv⟩ := h.scope.valid _ p hp
  have hf := h.scope.first _ p hp (Nat.le_refl _)
  have hparent : p.state.gcaFirst = p.loop.node.level := hf.1.symm.trans he.symm
  have href : (f.emit ctx tcLevel).2.firstlab = p.state.firstlab := (f.emit_first ctx tcLevel).1.trans hf.2
  have hsc := h.first_scatter hgsz hsymm hloop hauto
  rw [← he]
  apply Parent.scatter_stab hv hsc.2.1
  · rw [href]; exact (hv.first hparent).2
  · exact h.emit_parent hp
  · exact hsc.2.2

/-- Code two's scatter stabilizes its saved canonical ancestor. -/
theorem NodeInput.canon_stab {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hauto : let p := prepareOther ctx tcLevel f.level f.numcells f.entry
      (classify ctx f.level p.1 p.2.2.2.2.2).1 = .autoCanon)
    {p : Parent n} (hp : parents f.entry.gcaCanon = some p) :
    CellStab p.state.ptn f.entry.gcaCanon p.state.lab (f.emit ctx tcLevel).2.workperm := by
  obtain ⟨_, _, he, hv⟩ := h.scope.valid _ p hp
  have hf := h.scope.canonical _ p hp (Nat.le_refl _)
  have hparent : p.state.gcaCanon = p.loop.node.level := hf.1.symm.trans he.symm
  obtain ⟨_, _, _, hr⟩ := hv.canonical hparent
  have href : (f.emit ctx tcLevel).2.canonlab = p.state.canonlab := (f.emit_canon hauto).1.trans hf.2
  have hsc := h.canon_scatter hgsz hsymm hloop hauto
  rw [← he]
  apply Parent.scatter_stab hv hsc.2.1
  · rw [href]; exact hr
  · exact h.emit_parent hp
  · exact hsc.2.2

end Hex.GraphIso.Nauty.Max
