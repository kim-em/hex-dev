/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxPosition
public import HexGraphIso.Nauty.Policy.MaxBoundary
import all HexGraphIso.Nauty.Policy.MaxPosition
import all HexGraphIso.Nauty.Policy.MaxBoundary
import all HexGraphIso.Nauty.Policy.MaxSuspend
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Stabilization of a frozen sweep partition also holds in its current
ordering, since every cell has the same contents. -/
theorem SweepInput.stabilizes {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 index : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 cursor cell index
      st l bs fs parents) (hf : first = true) {γ : Array Nat} (hγ : γ ∈ st.genTrace) :
    CellStab st.ptn level st.lab γ := by
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have he := h.effect.ptn_eq h.base h.partition
  change st.ptn = (l.prepare ctx tcLevel).2.2.2.2.ptn at he
  have hperm := h.effect.perm

  have hstab := h.generators hf γ hγ
  rw [← he] at hperm hstab
  apply cellStab_of_scatter h.partition.ptnSize h.partition.labSize h.base.labSize
    (searchOk_end hn0 h.partition (by have := h.node.positive; rw [h.level_eq]; exact this))
    (cellsPerm_symm hperm) (cellsPerm_trans (cellsPerm_symm hperm) hstab)
  intro i hi
  have hsz : (l.prepare ctx tcLevel).2.2.2.2.lab.size = n := h.base.labSize
  rw [getElem!_map_of_lt _ _ (by rw [hsz]; exact hi)]

/-- Suspending the current sweep constructs every field of the child's
ancestor scope at the actual individualization. -/
theorem SweepInput.child_scope {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {first : Bool} {level numcells tc tv1 tv index : Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G ctx tcLevel fuel cfuel first level numcells tc tv1 (some tv) cell index
      st l bs fs parents) :
    let p : Parent n := ⟨l, st, tv, bs, fs⟩
    Scope G ctx tcLevel (level + 1) (l.codes ctx) bs
      (Nauty.child first level tc tv st) (parents.push p) := by
  intro p
  have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
  have hl : 1 ≤ level := by rw [h.level_eq]; exact h.node.positive
  have hch := (reachPolicy G ctx tcLevel hn0).child first level numcells tc tv cell st
    hl h.partition h.target (h.cursor_mem tv rfl)
  dsimp only [policy, Generic.Policy.child] at hch
  have hout : SearchOut G level level st (Nauty.child first level tc tv st) :=
    hch.2 _ ((SearchOut.refl G (level + 1) (level + 1) hch.1.reach).mono (by omega))
  have hlen : (l.codes ctx).length = level := by
    simp only [Loop.codes, List.length_append, List.length_singleton]
    rw [h.node.length, ← h.level_eq]
  have hchild : p.child ctx tcLevel =
      ⟨level + 1, numcells + 1, l.codes ctx, Nauty.child first level tc tv st⟩ := by
    simp only [p, Parent.child, h.first_eq, h.level_eq, h.numcells_eq, h.tc_eq]
  have hkey : (Nauty.child first level tc tv st).key ctx bs = st.key ctx bs := by
    cases first <;> rfl
  have hf : (Nauty.child first level tc tv st).firstlab = st.firstlab := by cases first <;> rfl
  have hc : (Nauty.child first level tc tv st).canonlab = st.canonlab := by cases first <;> rfl
  have hgc : (Nauty.child first level tc tv st).gcaCanon = st.gcaCanon := by cases first <;> rfl
  have hgf : (Nauty.child first level tc tv st).gcaFirst = st.gcaFirst := by cases first <;> rfl
  have htrace : (Nauty.child first level tc tv st).genTrace = st.genTrace := by cases first <;> rfl
  constructor
  · intro t ht htl
    by_cases he : t = level
    · refine ⟨p, ?_⟩
      simp only [Parents.push, p, ← h.level_eq, he, ↓reduceIte]
    · obtain ⟨q, hq⟩ := h.scope.complete t ht (by omega)
      exact ⟨q, by simpa only [Parents.push, p, ← h.level_eq, he, ↓reduceIte] using hq⟩
  · intro t q hq
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · rename_i he
      cases hq
      exact ⟨by omega, by omega, h.level_eq.symm.trans he.symm, h.suspend⟩
    · obtain ⟨ht, htl, he, hv⟩ := h.scope.valid t q hq
      exact ⟨ht, by omega, he, hv⟩
  · intro t q hq
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · cases hq; exact List.prefix_refl _
    · exact h.scope.codes t q hq
  · intro t q hq ht
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · omega
    · exact h.scope.code t q hq ht
  · intro t q hq
    rw [hkey]
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · cases hq; exact Generic.Grows.refl _
    · exact h.scope.grows t q hq
  · intro t q hq
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · rename_i he; cases hq; simpa only [he] using hout
    · obtain ⟨ht, htl, he, hv⟩ := h.scope.valid t q hq
      have hok := hv.partition
      rw [he] at hok
      exact extend_effect ht (by omega) hok h.partition (h.scope.effect t q hq) hout
  · intro t q hq
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · cases hq
      have hh := (p.picked h.suspend).2
      rw [hchild] at hh
      exact hh
    · exact h.child_chosen hq
  · intro t q hq ht
    rw [hgc] at ht ⊢
    rw [hc]
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · cases hq; exact ⟨rfl, rfl⟩
    · exact h.scope.canonical t q hq ht
  · intro t q hq ht
    rw [hgf] at ht ⊢
    rw [hf]
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · cases hq; exact ⟨rfl, rfl⟩
    · exact h.scope.first t q hq ht
  · have hh := h.child_boundaries
    change ∀ t q, (parents.push p) t = some q →
      (p.child ctx tcLevel).entry.noncheaplevel = q.state.noncheaplevel ∨
        t + 1 ≤ (p.child ctx tcLevel).entry.noncheaplevel at hh
    rw [hchild] at hh
    exact hh
  · intro t q hq hfirst γ hγ
    rw [htrace] at hγ
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · rename_i he; cases hq
      rw [he]
      exact h.stabilizes (h.first_eq.trans hfirst) hγ
    · exact h.scope.generators t q hq hfirst γ hγ
  · intro t q hq hc ht
    have hpos : 0 < st.canonlevel := by cases first <;> exact hc
    rw [hgf] at ht
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · rename_i he
      cases hq
      have hfirst : first = true := by
        cases hf : first with
        | true => rfl
        | false => have hh := (h.control hpos).2 hf; omega
      exact ⟨h.first_eq.symm.trans hfirst, by simp only [hfirst]; rfl⟩
    · have hfirst : first = false := by
        cases hf : first with
        | false => rfl
        | true =>
          have hh := (h.control hpos).1 hf
          have htl := (h.scope.valid t q hq).2.1
          omega
      have hh := h.scope.coset t q hq hpos ht
      exact ⟨hh.1, by rw [hfirst]; exact hh.2⟩
  · intro t q hq ht
    simp only [Parents.push, p, ← h.level_eq] at hq
    split at hq
    · rename_i he; cases hq
      obtain ⟨prev, hp, hc⟩ := h.parent (by omega)
      refine ⟨prev, ?_, hc⟩
      simpa only [Parents.push, p, ← h.level_eq, he,
        show level - 1 ≠ level by omega, ↓reduceIte] using hp
    · obtain ⟨prev, hp, hc⟩ := h.scope.chain t q hq ht
      have htl := (h.scope.valid t q hq).2.1
      refine ⟨prev, ?_, hc⟩
      simpa only [Parents.push, p, ← h.level_eq,
        show t - 1 ≠ level by omega, ↓reduceIte] using hp

end Hex.GraphIso.Nauty.Max
