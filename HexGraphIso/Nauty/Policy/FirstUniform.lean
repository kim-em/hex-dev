/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstCount
public import HexGraphIso.Nauty.Policy.FirstBounds
public import HexGraphIso.Nauty.Generation.Uniform
import all HexGraphIso.Nauty.Policy.FirstCount
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Lowering the all-same boundary requires the completed orbit count
and a guiding child whose boundary has reached its own entry. -/
theorem first_drop {ctx : Ctx n} {inf tcLevel fuel level numcells last tv : Nat}
    {st leaf : Search n}
    (hopen : (Generic.prepareFirst ctx tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv)
    (hp : let r := Generic.prepareFirst ctx tcLevel level numcells st
      Generic.FirstPath ctx tcLevel fuel (level + 1) (r.1 + 1)
        (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf)
    (hsame : (node true ctx inf tcLevel (fuel + 1) level numcells st).2.allsamelevel ≤ level) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let ch := node true ctx inf tcLevel fuel (level + 1) (r.1 + 1)
      (child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))
    let sr := sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat tv (some tv)
      r.2.2.1 0 (cheapCheck true level r.2.2.2.2)
    sr.1 = .done ∧ r.2.2.2.1 = sr.2.1 ∧ ch.2.allsamelevel = level + 1 := by
  have hfloor := (firstPath_floor (inf := inf) hp).1
  have hsameLoop := firstSweep_same (ctx := ctx) (tcLevel := tcLevel) (level := level)
    (inf := inf) (fuel := fuel) (cfuel := n)
    (numcells := (Generic.prepareFirst ctx tcLevel level numcells st).1)
    (tc := (Generic.prepareFirst ctx tcLevel level numcells st).2.1.toNat)
    (cell := (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1) (index := 0) horbit
  rw [node_first] at hsame
  simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ↓reduceIte, htv, Option.getD_some] at hsame
  dsimp only
  generalize hs : sweep true ctx inf tcLevel fuel (n + 1) level
    (Generic.prepareFirst ctx tcLevel level numcells st).1
    (Generic.prepareFirst ctx tcLevel level numcells st).2.1.toNat tv (some tv)
    (Generic.prepareFirst ctx tcLevel level numcells st).2.2.1 0
    (cheapCheck true level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2) = result
    at hsame hsameLoop ⊢
  obtain ⟨exit, index, out⟩ := result
  cases exit with
  | fuel => simp only [Id.run_pure] at hsame; dsimp only at hsameLoop; omega
  | unwind => simp only [Id.run_pure] at hsame; dsimp only at hsameLoop; omega
  | done =>
    dsimp only at hsame hsameLoop ⊢
    unfold afterSweep at hsame
    split at hsame
    · rename_i hc
      simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, hc.1, hsameLoop.symm.trans hc.2⟩
    · simp only [Id.run_pure] at hsame; omega

/-- The all-same boundary is justified by actual counted carriers. The
only search premises are contracts for strictly smaller node calls. -/
theorem firstPath_uniform {G : Colored n k} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hp : Generic.FirstPath { g := rowsOf G } tcLevel fuel level numcells st last leaf)
    (hn : ∀ f, f < fuel → (contract G tcLevel).nodeValid f
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel f))
    {cs bs fs : List Nat} {parents : Parents n}
    (hi : NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents)
    (hsame : (node true { g := rowsOf G } (n + 2) tcLevel fuel level numcells st).2.allsamelevel ≤ level) :
    ∃ targets key, Generation.Uniform { g := rowsOf G } tcLevel level
      (st.refined { g := rowsOf G } level numcells) targets key := by
  induction hp generalizing cs bs fs parents with
  | leaf fuel level numcells st hdisc =>
    have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
    have hit := refined_iter (ctx := { g := rowsOf G }) hn0 hi.frame.positive hi.frame.partition
    have hv := ((reachPolicy G { g := rowsOf G } tcLevel hn0).visit
      level numcells st hi.frame.positive hi.frame.partition).1
    have hc : bcount (st.refined { g := rowsOf G } level numcells).ptn level n = n :=
      hv.count.symm.trans hdisc
    refine ⟨[], _, Generation.Uniform.leaf hit ?_⟩
    intro q hq
    have hh : (List.range n).countP (fun q => decide
        ((st.refined { g := rowsOf G } level numcells).ptn[q]! ≤ level)) = (List.range n).length := by
      rw [List.length_range]
      exact hc
    exact of_decide_eq_true (List.countP_eq_length.mp hh q (List.mem_range.mpr hq))
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let ctx : Ctx n := { g := rowsOf G }
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let R := st.refined ctx level numcells
    let l : Loop n := ⟨⟨level, numcells, cs, st⟩, true⟩
    let ready := cheapCheck true level r.2.2.2.2
    let ch := child true level r.2.1.toNat tv ready
    let parent : Parent n := ⟨l, ready, tv, bs, fs⟩
    have htv' : r.2.2.1.nextElem none = some tv := htv
    have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
    have hpre : FirstPre G ctx level numcells st := hi.entry.1
    have hit := refined_iter (ctx := ctx) hn0 hi.frame.positive hi.frame.partition
    have hl := hi.frame.positive
    have hd := first_drop (inf := n + 2) hopen htv horbit tail hsame
    have hs : SweepInput G ctx tcLevel fuel (n + 1) true level r.1 r.2.1.toNat tv
        (some tv) r.2.2.1 0 ready l bs fs parents := by
      have hh := hi.first_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hopen
      change SweepInput G ctx tcLevel fuel (n + 1) true level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0 ready l bs fs parents at hh
      simpa only [htv', Option.getD_some] using hh
    have hc : NodeInput G ctx tcLevel fuel true
        ⟨level + 1, r.1 + 1, l.codes ctx, ch⟩ bs fs (parents.push parent) := by
      have hh := hs.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
      simpa only [Parent.child, parent, l, ch, Loop.prepare, r, ctx, Generic.prepareFirst,
        policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.chooseTarget,
        Bool.true_and, beq_self_eq_true, ↓reduceIte] using hh
    obtain ⟨targets, key, hu⟩ := ih (fun f hf => hn f (by omega)) hc (Nat.le_of_eq hd.2.2)
    have huf : Generation.Uniform ctx tcLevel (level + 1)
        (childSt ctx level R r.2.1.toNat tv) targets key := by
      change Generation.Uniform ctx tcLevel (level + 1) (ch.refined ctx (level + 1) (r.1 + 1)) targets key at hu
      rwa [firstChild_refined] at hu
    obtain ⟨e, o, hlt, hcell, hne, ho, hat⟩ := firstChild_offset hn0 hl hi.frame.partition htv
    change level < n at hlt
    change (r.2.1.toNat, e) ∈ cells R.ptn level n at hcell
    change r.2.1.toNat < e at hne
    change o ≤ e - r.2.1.toNat at ho
    change R.lab[r.2.1.toNat + o]! = tv at hat
    have hchoice := prepareFirst_choice hopen hit hpre.equitable
    have htarget : r.2.1.toNat = specTargetcell ctx R.lab R.ptn level tcLevel := by rw [hchoice]; rfl
    have hfields := l.prepare_frame ctx tcLevel
    have hplab : (l.prepare ctx tcLevel).2.2.2.2.lab = R.lab := hfields.2.1
    have hpptn : (l.prepare ctx tcLevel).2.2.2.2.ptn = R.ptn := hfields.2.2
    have hcell' : (r.2.1.toNat, r.2.1.toNat + r.2.2.2.1 - 1) ∈ cells R.ptn level n := by
      apply isCell_mem_cells
      · rw [← hpptn]; exact hs.window
      · rw [hit.ok.ptnSize]
        exact Nat.le_refl _
      · exact hit.ok.ptnEnd
      · have hh := hs.len
        have hr := hs.range
        change 2 ≤ r.2.2.2.1 at hh
        change r.2.1.toNat + r.2.2.2.1 ≤ n at hr
        omega
    have he : e = r.2.1.toNat + r.2.2.2.1 - 1 :=
      cells_eq_of_start (by rw [hit.ok.ptnSize]; exact Nat.le_refl _) hit.ok.ptnEnd hcell hcell'
    have hall := hs.full (hn fuel (Nat.lt_succ_self _)) (Nat.le_of_eq hd.2.1)
    refine ⟨r.2.1.toNat :: targets, ⟨R.longcode :: key.codes, key.rows⟩,
      Generation.Uniform.carriers hit hlt (size_rowsOf G) hcell hne htarget ho ?_ (hat ▸ huf)⟩
    intro o' ho'
    have hm : R.lab[r.2.1.toNat + o']! ∈ segN (l.prepare ctx tcLevel).2.2.2.2.lab
        r.2.1.toNat (l.prepare ctx tcLevel).2.2.2.1 := by
      rw [hplab]
      apply mem_segN_iff.mpr
      refine ⟨o', ?_, rfl⟩
      change o' < r.2.2.2.1
      omega
    obtain ⟨γ, hg, hstab, hmap⟩ := hall _ hm
    rw [hpptn, hplab] at hstab
    exact ⟨γ, hg, hstab, hmap.trans hat.symm⟩

end Hex.GraphIso.Nauty.Max
