/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Invariant.Singleton
import all HexGraphIso.Nauty.Invariant.Autos
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Preparing a node preserves its entry singletons and their vertices. -/
theorem Loop.singleton {G : Colored n k} {ctx : Ctx n} {tcLevel a : Nat}
    {l : Loop n} (h : l.node.Valid G)
    (ha : IsCell l.node.entry.ptn l.node.level a 1) :
    IsCell (l.prepare ctx tcLevel).2.2.2.2.ptn l.node.level a 1 ∧
      (l.prepare ctx tcLevel).2.2.2.2.lab[a]! = l.node.entry.lab[a]! := by
  have hn0 : 0 < n := by have := h.positive; have := h.depth; omega
  obtain ⟨_, hl, hp⟩ := l.prepare_frame ctx tcLevel
  rw [hl, hp]
  have hs : l.node.entry.lab.size = l.node.entry.ptn.size :=
    h.partition.labSize.trans h.partition.ptnSize.symm
  have hend := searchOk_end hn0 h.partition h.positive
  exact ⟨isCell_refine_one h.partition.ptnSize.symm hs hend ha,
    refine_fixes_singleton (Nat.le_of_eq h.partition.ptnSize.symm) hs hend ha⟩

/-- A saved parent's selected vertex is a singleton at its actual child entry. -/
theorem Parent.picked {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel) :
    let ch := p.child ctx tcLevel
    let tc := (p.loop.prepare ctx tcLevel).2.1.toNat
    IsCell ch.entry.ptn ch.level tc 1 ∧ ch.entry.lab[tc]! = p.chosen := by
  intro ch tc
  have hc := isCell_of_low h.effect.low h.cell
  change IsCell p.state.ptn p.loop.node.level tc (p.loop.prepare ctx tcLevel).2.2.2.1 at hc
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (mem_windowSet.mp h.chosen).2
  have hr := h.range
  have hpsz : p.state.ptn.size = n := h.partition.ptnSize
  have hlsz : p.state.lab.size = n := h.partition.labSize
  have hs : tc < p.state.ptn.size := by rw [hpsz]; have := h.len; omega
  have hi : LabInj p.state.lab p.state.lab.size := by
    rw [hlsz]
    exact labInj_of_reach h.partition.labSize
      (by have := h.node.positive; have := h.node.depth; omega) h.partition.reach
  have ht : tc + o < p.state.lab.size := by rw [hlsz]; omega
  constructor
  · have hh := isCell_breakout_target (n := n) (lab := p.state.lab) (tv := p.chosen) hs hc.2.1
    dsimp only [ch, Parent.child]
    cases hf : p.loop.first <;> simpa only [Nauty.child, hf, Bool.false_eq_true,
      ↓reduceIte] using hh
  · have hh := breakout_at_target (n := n) (ptn := p.state.ptn)
      (level := p.loop.node.level) hi ht
    rw [hv] at hh
    dsimp only [ch, Parent.child]
    cases hf : p.loop.first <;> simpa only [Nauty.child, hf, Bool.false_eq_true,
      ↓reduceIte] using hh

/-- A saved child singleton remains present when its node's sweep resumes. -/
theorem Parent.singleton {G : Colored n k} {ctx : Ctx n} {tcLevel a : Nat}
    {p : Parent n} (h : p.Valid G ctx tcLevel)
    (ha : IsCell p.loop.node.entry.ptn p.loop.node.level a 1) :
    IsCell p.state.ptn p.loop.node.level a 1 :=
  isCell_of_low h.effect.low (p.loop.singleton h.node ha).1

/-- The saved ancestor chain supplies every earlier selected singleton.
No additional singleton invariant is required at the sweep entry. -/
theorem SweepInput.singletons {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 index : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 cursor cell index
      st l bs fs parents) {t : Nat} {p : Parent n} (hp : parents t = some p) :
    IsCell st.ptn level (p.loop.prepare ctx tcLevel).2.1.toNat 1 := by
  obtain ⟨ht, htl, hpl, hvalid⟩ := h.scope.valid t p hp
  have hsingle := (p.picked hvalid).1
  by_cases he : t + 1 = level
  · obtain ⟨q, hq, hchild⟩ := h.parent (by omega)
    have ht' : level - 1 = t := by omega
    rw [ht', hp] at hq
    cases hq
    rw [hchild] at hsingle
    have hs := (l.singleton (ctx := ctx) (tcLevel := tcLevel) h.node hsingle).1
    rw [← h.level_eq] at hs
    exact isCell_of_low h.effect.low hs
  · obtain ⟨q, hq⟩ := h.scope.complete (t + 1) (by omega) (by omega)
    obtain ⟨_, _, hql, hqvalid⟩ := h.scope.valid (t + 1) q hq
    obtain ⟨prev, hprev, hchild⟩ := h.scope.chain (t + 1) q hq (by omega)
    simp only [Nat.add_sub_cancel, hp, Option.some.injEq] at hprev
    subst prev
    rw [hchild] at hsingle
    have hs := q.singleton hqvalid hsingle
    rw [hql] at hs
    have hs' := isCell_of_low (h.scope.effect (t + 1) q hq).low hs
    exact isCell_one_mono hs' (by omega)

/-- Individualizing the next target preserves all earlier chosen vertices. -/
theorem SweepInput.child_chosen {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents) {t : Nat} {p : Parent n} (hp : parents t = some p) :
    (Nauty.child first level tc tv st).lab[(p.loop.prepare ctx tcLevel).2.1.toNat]! = p.chosen := by
  have hs := h.singletons hp
  obtain ⟨len, hc, hm⟩ := h.target
  obtain ⟨hc, hlen, hr⟩ := hc (mem_ne_empty (h.cursor_mem tv rfl))
  obtain ⟨o, ho, hv⟩ := mem_segN_iff.mp (hm tv (h.cursor_mem tv rfl))
  change st.lab[tc + o]! = tv at hv
  have hne : (p.loop.prepare ctx tcLevel).2.1.toNat ≠ tc := by
    intro he
    rw [he] at hs
    rcases isCell_disjoint_or_eq hs hc with hleft | hright | heq <;> omega
  have hsz : st.lab.size = n := h.partition.labSize
  have hi : LabInj st.lab st.lab.size := by
    rw [hsz]
    exact labInj_of_reach h.partition.labSize
      (by have := h.node.positive; have := h.node.depth; omega) h.partition.reach
  have hh := breakout_misses_singleton (n := n) (ptn := st.ptn) (level := level)
    hi (by rw [hsz]; omega) (singleton_outside_cell hs hc hne ho)
  rw [hv] at hh
  have he : (Nauty.child first level tc tv st).lab[(p.loop.prepare ctx tcLevel).2.1.toNat]! =
      st.lab[(p.loop.prepare ctx tcLevel).2.1.toNat]! := by
    cases first <;> exact hh
  exact he.trans (h.scope.chosen t p hp)

/-- A finer partition effect composes with a saved ancestor's effect,
including references installed within the finer partition. -/
theorem extend_effect {G : Colored n k} {t level nc mc : Nat} {base st out : Search n}
    (ht : 1 ≤ t) (htl : t ≤ level) (hb : SearchOk G t nc base)
    (hs : SearchOk G level mc st) (he : SearchOut G t t base st)
    (ho : SearchOut G level level st out) :
    SearchOut G t t base out := by
  have hn0 : 0 < n := by have := hb.bc; have := bcount_le base.ptn t n; omega
  have hp : ∀ lab, lab.size = st.lab.size → cellsPerm st.ptn level st.lab lab →
      cellsPerm base.ptn t st.lab lab := by
    intro lab hsize hperm
    exact cellsPerm_coarsen he.ptnSize.symm
      (hs.labSize.trans hs.ptnSize.symm)
      (hsize.trans (hs.labSize.trans hs.ptnSize.symm)) hperm
      (searchOk_end hn0 hs (by omega)) (searchOk_end hn0 hb ht)
      (fun q hq => by rw [he.low q (Or.inl hq)]; omega)
  refine ⟨ho.labSize.trans he.labSize, ho.ptnSize.trans he.ptnSize, ho.reach,
    ?_, cellsPerm_trans he.perm (hp _ ho.labSize ho.perm), ?_, ?_, ?_⟩
  · intro q hq
    rcases hq with hq | hq
    · have hh := he.low q (Or.inl hq)
      rw [ho.low q (Or.inl (by omega)), hh]
    · have hh := ho.low q (Or.inr (by omega))
      rw [hh, he.low q (Or.inr (by omega))]
  · rcases ho.firstStore with hf | ⟨hs, hf⟩
    · rw [hf]; exact he.firstStore
    · exact Or.inr ⟨hs.trans he.labSize, cellsPerm_trans he.perm (hp _ hs hf)⟩
  · rcases ho.canonStore with hc | ⟨hs, hc⟩
    · rw [hc]; exact he.canonStore
    · exact Or.inr ⟨hs.trans he.labSize, cellsPerm_trans he.perm (hp _ hs hc)⟩
  · rcases ho.canon with hc | hc
    · rw [hc]; exact he.canon
    · exact Or.inr hc

end Hex.GraphIso.Nauty.Max
