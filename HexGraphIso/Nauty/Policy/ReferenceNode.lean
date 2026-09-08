/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ReferenceLoop
public import HexGraphIso.Nauty.Policy.ReferenceDescent
import all HexGraphIso.Nauty.Policy.ReferenceLoop
import all HexGraphIso.Nauty.Policy.ReferenceDescent
import all HexGraphIso.Nauty.Policy.ReferenceSweep
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.FirstWitness
import all HexGraphIso.Nauty.Policy.MaxNode
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Generation.RefPath
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- The actual off-path input supplies the complete mathematical tree
invariant after refinement. -/
theorem NodeInput.reference_tree {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents) :
    Generation.TreeOk ctx f.level (f.entry.refined ctx f.level f.numcells) := by
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hv := ((reachPolicy G ctx tcLevel hn0).visit f.level f.numcells f.entry
    h.frame.positive h.frame.partition).1
  refine ⟨refined_iter hn0 h.frame.positive h.frame.partition, h.entry.1.equitable, hv.count.symm, ?_⟩
  have hc := hv.bc
  rw [← hv.count] at hc
  exact hc

/-- A matching internal node prepares exactly the specification target
and retains first-reference agreement, regardless of the canonical comparison. -/
theorem Loop.reference_prepare {ctx : Ctx n} {tcLevel tc : Nat} {f : Frame n}
    {targets : List Nat} {key : Key n}
    (ht : Generation.TreeOk ctx f.level (f.entry.refined ctx f.level f.numcells))
    (hm : Generation.Matches ctx f.level f.entry.view (tc :: targets) key)
    (hp : Generation.HasLeaf ctx tcLevel f.level (f.entry.refined ctx f.level f.numcells)
      (tc :: targets) key)
    (heq : f.entry.eqlevFirst = f.level - 1)
    (hn : (f.entry.refined ctx f.level f.numcells).numcells < n) :
    let l : Loop n := ⟨f, false⟩
    let p := l.prepare ctx tcLevel
    let rs := f.entry.refined ctx f.level f.numcells
    let mt := specMaketargetcell ctx rs.lab rs.ptn f.level tcLevel
    (let q := prepareOther ctx tcLevel f.level f.numcells f.entry;
      (classify ctx f.level q.1 q.2.2.2.2.2).1 = .internal) ∧
    p.2.1 = Int.ofNat mt.1 ∧ p.2.2.1 = mt.2.1 ∧ p.2.2.2.1 = mt.2.2 ∧
    p.2.2.2.2.eqlevFirst = f.level ∧ p.2.2.2.2.reference = f.entry.reference ∧
    p.2.2.2.2.allsamelevel = f.entry.allsamelevel ∧
    p.2.2.2.2.gcaFirst = f.entry.gcaFirst ∧ p.2.2.2.2.gcaCanon = f.entry.gcaCanon := by
  intro l p rs mt
  change rs.numcells < n at hn
  let compared := compareCodes f.level rs.longcode (Engine.visit ctx f.level f.numcells f.entry).2.2
  have hfields : compared.lab = rs.lab ∧ compared.ptn = rs.ptn ∧
      compared.reference = f.entry.reference ∧ compared.allsamelevel = f.entry.allsamelevel ∧
      compared.gcaFirst = f.entry.gcaFirst ∧ compared.gcaCanon = f.entry.gcaCanon := by
    dsimp only [compared]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run]
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have he : compared.eqlevFirst = f.level := by
    have hh := (hm.stateEq (out := (Engine.visit ctx f.level f.numcells f.entry).2.2.view) rfl rfl rfl).prep hp heq
    rw [← view_compareCodes] at hh
    exact hh
  have hm' := matches_reference hm hfields.2.2.1
  have hchoice := matching_target ht.it ht.eqt hfields.1 hfields.2.1 hn hm' hp he
  change chooseTarget false ctx tcLevel f.level rs.numcells compared =
    (Int.ofNat mt.1, mt.2.1, mt.2.2, { compared with tctotal := compared.tctotal + mt.2.2 }) at hchoice
  have hp' : p = (rs.numcells, Int.ofNat mt.1, mt.2.1, mt.2.2,
      cheapCheck false f.level { compared with tctotal := compared.tctotal + mt.2.2 }) := by
    change (let q := chooseTarget false ctx tcLevel f.level rs.numcells compared
      (rs.numcells, q.1, q.2.1, q.2.2.1, cheapCheck false f.level q.2.2.2)) = _
    rw [hchoice]
  constructor
  · change (classify ctx f.level rs.numcells
      (chooseTarget false ctx tcLevel f.level rs.numcells compared).2.2.2).1 = .internal
    rw [hchoice, classify_eq]
    simp only [he, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      bne_iff_ne.mpr (Nat.ne_of_lt hn)]
  · rw [hp']
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold cheapCheck
    split <;> exact ⟨he, hfields.2.2.1, hfields.2.2.2⟩

end Hex.GraphIso.Nauty.Engine.Max
