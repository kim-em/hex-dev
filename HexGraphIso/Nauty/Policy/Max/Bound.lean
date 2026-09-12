/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Max.Choice
public import HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Choice
import all HexGraphIso.Nauty.Policy.Max.Prepare
import all HexGraphIso.Nauty.Policy.Max.Context
import all HexGraphIso.Nauty.Policy.Max.Contract
import all HexGraphIso.Nauty.Policy.Max.Frame
import all HexGraphIso.Nauty.Policy.Comparison
import all HexGraphIso.Nauty.Policy.Prune
import all HexGraphIso.Nauty.Policy.CodeCalls
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Policy.First.History
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- At the specification target, the complete sweep bound is exactly
its node's key, including the common refinement-code prefix. -/
theorem Loop.bound_eq {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat} {l : Loop n}
    (h : l.node.Valid G)
    (hcell : IsCell (l.prepare ctx tcLevel).2.2.2.2.ptn l.node.level
      (l.prepare ctx tcLevel).2.1.toNat (l.prepare ctx tcLevel).2.2.2.1)
    (hlen : 2 ≤ (l.prepare ctx tcLevel).2.2.2.1)
    (hrange : (l.prepare ctx tcLevel).2.1.toNat + (l.prepare ctx tcLevel).2.2.2.1 ≤ n)
    (hselected : specTargetcell ctx
      (l.node.entry.refined ctx l.node.level l.node.numcells).lab
      (l.node.entry.refined ctx l.node.level l.node.numcells).ptn l.node.level tcLevel =
        (l.prepare ctx tcLevel).2.1.toNat) :
    l.node.key ctx tcLevel = l.bound ctx tcLevel := by
  let r := l.node.entry.refined ctx l.node.level l.node.numcells
  let p := l.prepare ctx tcLevel
  change 2 ≤ p.2.2.2.1 at hlen
  change p.2.1.toNat + p.2.2.2.1 ≤ n at hrange
  have hn0 : 0 < n := by have := h.positive; have := h.depth; omega
  have hit := refined_iter (ctx := ctx) hn0 h.positive h.partition
  obtain ⟨hnc, hl, hp⟩ := l.prepare_frame ctx tcLevel
  change p.1 = r.numcells at hnc
  change p.2.2.2.2.lab = r.lab at hl
  change p.2.2.2.2.ptn = r.ptn at hp
  change specTargetcell ctx r.lab r.ptn l.node.level tcLevel = p.2.1.toNat at hselected
  have hc : IsCell r.ptn l.node.level p.2.1.toNat p.2.2.2.1 := by rw [← hp]; exact hcell
  have hend := cellEnd_of_isCell hc (by omega : 1 < p.2.2.2.1)
    (by rw [hit.ok.ptnSize]; exact hrange)
  have hsize : (specMaketargetcell ctx r.lab r.ptn l.node.level tcLevel).2.2 =
      (p.2.2.2.1 - 1) + 1 := by
    simp only [specMaketargetcell, hselected, hend]
    omega
  have hdisc : discreteAt r.ptn l.node.level n = false := by
    rw [discreteAt, List.all_eq_false]
    refine ⟨(p.2.1.toNat, p.2.1.toNat + p.2.2.2.1 - 1),
      isCell_mem_cells hc (Nat.le_of_eq hit.ok.ptnSize.symm) hit.ok.ptnEnd
        (by omega), ?_⟩
    simpa using (Nat.ne_of_lt (show p.2.1.toNat < p.2.1.toNat + p.2.2.2.1 - 1 by omega))
  have hh := specNode_internal (tcLevel := tcLevel) (fuel := n - l.node.level)
    l.node.codes hdisc hsize
  have hd := h.depth
  rw [Frame.key, show n + 1 - l.node.level = n - l.node.level + 1 by omega, hh]
  have hchild : ∀ o, prefixKey (l.node.codes ++ [r.longcode])
      (specChild ctx tcLevel (n - l.node.level) l.node.level
        l.node.entry.lab l.node.entry.ptn l.node.entry.active l.node.numcells o) =
      l.key ctx tcLevel p.2.2.2.2.lab[p.2.1.toNat + o]! := by
    intro o
    dsimp only [specChild]
    change prefixKey (l.node.codes ++ [r.longcode])
      (vertexKey ctx tcLevel (n - l.node.level) l.node.level r.lab r.ptn
        (specTargetcell ctx r.lab r.ptn l.node.level tcLevel) r.numcells
        r.lab[specTargetcell ctx r.lab r.ptn l.node.level tcLevel + o]!) = _
    rw [hselected, ← hnc, ← hl, ← hp]
    rfl
  change keysMax _ ((List.range (p.2.2.2.1 - 1)).map _) = _
  change keysMax (prefixKey (l.node.codes ++ [r.longcode])
    (specChild ctx tcLevel (n - l.node.level) l.node.level l.node.entry.lab l.node.entry.ptn
      l.node.entry.active l.node.numcells 0))
    ((List.range (p.2.2.2.1 - 1)).map (fun o => prefixKey (l.node.codes ++ [r.longcode])
      (specChild ctx tcLevel (n - l.node.level) l.node.level l.node.entry.lab l.node.entry.ptn
        l.node.entry.active l.node.numcells (o + 1)))) = _
  simp only [hchild, Nat.add_zero]
  simp only [Loop.bound, List.range'_eq_map_range, List.map_map, Function.comp_def,
    Nat.add_comm 1]
  rfl

/-- A downward code comparison bounds the actual sweep even when its
hinted target differs from the specification's target. -/
theorem Loop.bound_dominated {ctx : Ctx n} {tcLevel : Nat} {l : Loop n} {bs fs : List Nat}
    (h : Comparison ctx (l.codes ctx) bs fs (l.prepare ctx tcLevel).2.2.2.2)
    (hc : (l.prepare ctx tcLevel).2.2.2.2.compCanon < 0) :
    Generic.Covers (l.bound ctx tcLevel) ((l.prepare ctx tcLevel).2.2.2.2.key ctx bs) := by
  refine ⟨incKey ctx bs (l.prepare ctx tcLevel).2.2.2.2.canonlab, ?_, ?_⟩
  · simp only [SearchState.key, h.nonempty, ↓reduceIte]
  · have hv : ∀ v, keyLe (l.key ctx tcLevel v)
        (incKey ctx bs (l.prepare ctx tcLevel).2.2.2.2.canonlab) :=
      fun v => h.canonical.prefix_le hc _
    exact keysMax_le (hv _) (fun key hk => by obtain ⟨v, _, rfl⟩ := List.mem_map.mp hk; exact hv _)

/-- Actual off-path preparation supplies the comparison of the sweep's
full code prefix, also during upward code-storage overwrites. -/
theorem Loop.comparison {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {l : Loop n} {bs fs : List Nat} (h : l.node.Valid G) (hf : l.first = false)
    (he : Entry G ctx tcLevel l.first l.node bs fs) :
    Comparison ctx (l.codes ctx) bs fs (l.prepare ctx tcLevel).2.2.2.2 := by
  rw [hf] at he
  have hh := he.2.prepare (tcLevel := tcLevel) (numcells := l.node.numcells)
    (by have := h.length; have := h.depth; omega)
  rw [h.length] at hh
  have hc := hh.1.cheap false l.node.level
  simpa only [Loop.prepare, Loop.codes, Frame.code, hf, Bool.false_eq_true, ↓reduceIte,
    prepareOther, visit, Id.run_pure] using hc

/-- A sweep's upper bound implies the node's upper bound, using the
actual code comparison in the dominated hinted arm. -/
theorem Loop.node_bound {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {l : Loop n} {bs fs : List Nat} {after : Option (Key n)}
    (h : l.node.Valid G) (he : Entry G ctx tcLevel l.first l.node bs fs)
    (hcell : IsCell (l.prepare ctx tcLevel).2.2.2.2.ptn l.node.level
      (l.prepare ctx tcLevel).2.1.toNat (l.prepare ctx tcLevel).2.2.2.1)
    (hlen : 2 ≤ (l.prepare ctx tcLevel).2.2.2.1)
    (hrange : (l.prepare ctx tcLevel).2.1.toNat + (l.prepare ctx tcLevel).2.2.2.1 ≤ n)
    (hnc : (l.prepare ctx tcLevel).1 < n)
    (hb : Generic.Bounded (l.bound ctx tcLevel)
      ((l.prepare ctx tcLevel).2.2.2.2.key ctx bs) after) :
    Generic.Bounded (l.node.key ctx tcLevel) (l.node.entry.key ctx bs) after := by
  have hbefore := l.prepare_key ctx tcLevel bs
  by_cases hn : l.first = false ∧ (l.prepare ctx tcLevel).2.2.2.2.compCanon < 0
  · have hc := l.bound_dominated (l.comparison h hn.1 he) hn.2
    obtain ⟨b, hread, hle⟩ := hc
    refine ⟨?_, hbefore ▸ hb.grows⟩
    intro a ha
    have hu := hb.upper a ha
    rw [hread, incMax, keyMax_eq_left hle] at hu
    have hstore : l.node.entry.key ctx bs = some b := hbefore.symm.trans hread
    rw [hstore]
    exact keyLe_trans hu (keyLe_iff.mpr (keyMax_not_lt_left b _))
  · have hs : specTargetcell ctx
        (l.node.entry.refined ctx l.node.level l.node.numcells).lab
        (l.node.entry.refined ctx l.node.level l.node.numcells).ptn l.node.level tcLevel =
          (l.prepare ctx tcLevel).2.1.toNat := by
      cases hf : l.first with
      | true =>
        -- The first target has no hint, independently of its unused comparison field.
        have hp : FirstPre G ctx l.node.level l.node.numcells l.node.entry := by
          rw [hf] at he; exact he.1
        have hi := refined_iter (ctx := ctx)
          (by have := h.positive; have := h.depth; omega) h.positive h.partition
        have hm := maketargetcell_eq_spec (tcLevel := tcLevel) hp.equitable
          hi.ok.labOk hi.ok.labSize hi.ok.ptnSize hi.ok.ptnEnd
        change maketargetcell ctx (visit ctx l.node.level l.node.numcells l.node.entry).2.2.lab
          (visit ctx l.node.level l.node.numcells l.node.entry).2.2.ptn l.node.level tcLevel (-1) = _ at hm
        have hne : (visit ctx l.node.level l.node.numcells l.node.entry).1 ≠ n := Nat.ne_of_lt hnc
        dsimp only [Loop.prepare]
        simp only [hf, ↓reduceIte, chooseTarget, Bool.not_true, Bool.false_and,
          Bool.false_eq_true, bne_iff_ne.mpr hne, Id.run_pure, recordFirst]
        rw [hm]
        rfl
      | false =>
        have hnonneg : 0 ≤ (l.prepare ctx tcLevel).2.2.2.2.compCanon := by
          have hh : ¬ (l.prepare ctx tcLevel).2.2.2.2.compCanon < 0 := fun ht => hn ⟨hf, ht⟩
          omega
        rw [hf] at he
        have hi := refined_iter (ctx := ctx)
          (by have := h.positive; have := h.depth; omega) h.positive h.partition
        let v := visit ctx l.node.level l.node.numcells l.node.entry
        let c := compareCodes l.node.level v.2.1 v.2.2
        have hcc : c.compCanon = (l.prepare ctx tcLevel).2.2.2.2.compCanon := by
          dsimp only [Loop.prepare]
          simp only [hf, Bool.false_eq_true, ↓reduceIte, cheapCheck,
            apply_ite SearchState.compCanon, ite_self]
          rw [chooseTarget_fields]
        have hl : c.lab = (l.node.entry.refined ctx l.node.level l.node.numcells).lab :=
          (compareCodes_frame _ _ _).1
        have hp : c.ptn = (l.node.entry.refined ctx l.node.level l.node.numcells).ptn :=
          (compareCodes_frame _ _ _).2.1
        have hh := chooseTarget_unhinted (ctx := ctx) (tcLevel := tcLevel) (st := c) (show v.1 < n from hnc)
          (by omega) (by rw [hl, hp]; exact he.1.equitable)
          (by rw [hl]; exact hi.ok.labOk) (by rw [hl]; exact hi.ok.labSize)
          (by rw [hp]; exact hi.ok.ptnSize) (by rw [hp]; exact hi.ok.ptnEnd)
        dsimp only [Loop.prepare]
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        change _ = (chooseTarget false ctx tcLevel l.node.level v.1 c).1.toNat
        rw [hh, hl, hp]
        rfl
    rw [← l.bound_eq h hcell hlen hrange hs, hbefore] at hb
    exact hb

end Hex.GraphIso.Nauty.Max
