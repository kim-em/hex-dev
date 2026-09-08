/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstUniform
public import HexGraphIso.Nauty.Policy.GenerationRef
public import HexGraphIso.Nauty.Generation.RefPath
import all HexGraphIso.Nauty.Generation.Uniform
import all HexGraphIso.Nauty.Policy.FirstUniform
import all HexGraphIso.Nauty.Policy.GenerationRef
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- Stored matching depends only on the three first-reference fields. -/
theorem matches_reference {ctx : Ctx n} {level : Nat} {st out : Search n}
    {targets : List Nat} {key : Key n}
    (h : Generation.Matches ctx level st.view targets key)
    (he : out.reference = st.reference) :
    Generation.Matches ctx level out.view targets key :=
  h.stateEq (congrArg Prod.fst he) (congrArg (fun r => r.2.1) he)
    (congrArg (fun r => r.2.2) he)

/-- The saved first reference retains uniformity along its actual descent,
at precisely the all-same boundary returned by the complete engine call. -/
theorem firstPath_witness {G : Colored n k} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hp : Generic.FirstPath { g := rowsOf G } tcLevel fuel level numcells st last leaf)
    (hn : ∀ f, f < fuel → (contract G tcLevel).nodeValid f
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel f))
    {cs bs fs : List Nat} {parents : Parents n}
    (hi : NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents) :
    let ctx : Ctx n := { g := rowsOf G }
    let out := (node true ctx (n + 2) tcLevel fuel level numcells st).2
    ∃ targets key,
      Generation.RefPath ctx tcLevel out.allsamelevel level
        (st.refined ctx level numcells) targets key ∧
      Generation.Matches ctx level out.view targets key := by
  have uniformCase : ∀ {fuel level numcells last st leaf cs bs fs parents},
      (hp : Generic.FirstPath { g := rowsOf G } tcLevel fuel level numcells st last leaf) →
      (∀ f, f < fuel → (contract G tcLevel).nodeValid f
        (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel f)) →
      NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents →
      (node true { g := rowsOf G } (n + 2) tcLevel fuel level numcells st).2.allsamelevel ≤ level →
      ∃ targets key,
        Generation.RefPath { g := rowsOf G } tcLevel
          (node true { g := rowsOf G } (n + 2) tcLevel fuel level numcells st).2.allsamelevel
          level (st.refined { g := rowsOf G } level numcells) targets key ∧
        Generation.Matches { g := rowsOf G } level
          (node true { g := rowsOf G } (n + 2) tcLevel fuel level numcells st).2.view targets key := by
    intro fuel level numcells last st leaf cs bs fs parents hp hn hi hb
    have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
    obtain ⟨href, _⟩ := firstRef_of_path (inf := n + 2) hn0 (rowsOf_symm G) hp
      hi.frame.positive hi.frame.partition hi.entry.1.equitable hi.entry.1.targets hi.entry.1.codes
    obtain ⟨targets, key, ho, hm⟩ := href.occurs
    obtain ⟨ut, uk, hu⟩ := firstPath_uniform hp hn hi hb
    obtain ⟨rfl, rfl⟩ := hu targets key ho
    exact ⟨targets, key, ho.uniformPath (refined_iter hn0 hi.frame.positive hi.frame.partition) hu, hm⟩
  induction hp generalizing cs bs fs parents with
  | leaf fuel level numcells st hdisc =>
    apply uniformCase (.leaf fuel level numcells st hdisc) hn hi
    rw [node_first]
    simp only [hdisc, beq_self_eq_true, ↓reduceIte, firstterminal, Id.run_pure]
    exact Nat.le_refl _
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let ctx : Ctx n := { g := rowsOf G }
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let R := st.refined ctx level numcells
    let l : Loop n := ⟨⟨level, numcells, cs, st⟩, true⟩
    let ready := cheapCheck true level r.2.2.2.2
    let ch := child true level r.2.1.toNat tv ready
    let childOut := (node true ctx (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch).2
    let out := (node true ctx (n + 2) tcLevel (fuel + 1) level numcells st).2
    have hp : Generic.FirstPath ctx tcLevel (fuel + 1) level numcells st last leaf :=
      .step hopen htv horbit tail
    by_cases hb : out.allsamelevel ≤ level
    · exact uniformCase hp hn hi hb
    have htv' : r.2.2.1.nextElem none = some tv := htv
    have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
    have hit := refined_iter (ctx := ctx) hn0 hi.frame.positive hi.frame.partition
    have hs : SweepInput G ctx tcLevel fuel (n + 1) true level r.1 r.2.1.toNat tv
        (some tv) r.2.2.1 0 ready l bs fs parents := by
      have hh := hi.first_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hopen
      change SweepInput G ctx tcLevel fuel (n + 1) true level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0 ready l bs fs parents at hh
      simpa only [htv', Option.getD_some] using hh
    let parent : Parent n := ⟨l, ready, tv, bs, fs⟩
    have hc : NodeInput G ctx tcLevel fuel true
        ⟨level + 1, r.1 + 1, l.codes ctx, ch⟩ bs fs (parents.push parent) := by
      have hh := hs.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
      simpa only [Parent.child, parent, l, ch, Loop.prepare, r, ctx, Generic.prepareFirst,
        policy, Generic.Policy.visit, Generic.Policy.recordFirst, Generic.Policy.chooseTarget,
        Bool.true_and, beq_self_eq_true, ↓reduceIte] using hh
    obtain ⟨targets, key, href, hm⟩ := ih (fun f hf => hn f (by omega)) hc
    change Generation.RefPath ctx tcLevel childOut.allsamelevel (level + 1)
      (ch.refined ctx (level + 1) (r.1 + 1)) targets key at href
    have hboundary : out.allsamelevel = childOut.allsamelevel := by
      have hsame := firstSweep_same (ctx := ctx) (inf := n + 2) (tcLevel := tcLevel)
        (fuel := fuel) (cfuel := n) (level := level) (numcells := r.1)
        (tc := r.2.1.toNat) (cell := r.2.2.1) (index := 0) horbit
      change out.allsamelevel = childOut.allsamelevel
      dsimp only [out, ctx]
      rw [node_first]
      simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ↓reduceIte, htv,
        Option.getD_some]
      generalize he : sweep true ctx (n + 2) tcLevel fuel (n + 1) level r.1 r.2.1.toNat
        tv (some tv) r.2.2.1 0 ready = result at hsame ⊢
      obtain ⟨exit, index, result⟩ := result
      cases exit with
      | fuel => exact hsame
      | unwind => exact hsame
      | done =>
        dsimp only
        unfold afterSweep
        split
        · rename_i hd
          have hout : out.allsamelevel = level := by
            dsimp only [out, ctx]
            rw [node_first]
            simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ↓reduceIte, htv,
              Option.getD_some]
            rw [he]
            change (afterSweep true level r.2.2.2.1 index result).allsamelevel = level
            have hd' : (true && r.2.2.2.1 == index && result.allsamelevel == level + 1) = true := hd
            simp only [afterSweep, hd', ↓reduceIte]
            simp only [Bool.true_and, Bool.and_eq_true, beq_iff_eq] at hd'
            omega
          exact (hb (Nat.le_of_eq hout)).elim
        · exact hsame
    have hr : out.reference = childOut.reference :=
      (firstPath_reference hp).trans (firstPath_reference tail).symm
    have hm' : Generation.Matches ctx (level + 1) out.view targets key :=
      matches_reference hm hr
    obtain ⟨e, o, hlt, hcell, hne, ho, hat⟩ :=
      firstChild_offset hn0 hi.frame.positive hi.frame.partition htv
    change level < n at hlt
    change (r.2.1.toNat, e) ∈ cells R.ptn level n at hcell
    change r.2.1.toNat < e at hne
    change o ≤ e - r.2.1.toNat at ho
    change R.lab[r.2.1.toNat + o]! = tv at hat
    have hchoice := prepareFirst_choice hopen hit hi.entry.1.equitable
    have ht : r.2.1.toNat = specTargetcell ctx R.lab R.ptn level tcLevel := by rw [hchoice]; rfl
    rw [firstChild_refined, ← hat, ← hboundary] at href
    have hprefix := firstPath_reference (inf := n + 2) hp
    have hl : level + 1 ≤ last := by
      have hh : ∀ {f l nc z : Nat} {s q : Search n}, Generic.FirstPath ctx tcLevel f l nc s z q → l ≤ z := by
        intro f l nc z s q hp
        induction hp with
        | leaf => exact Nat.le_refl _
        | step _ _ _ _ ih => omega
      exact hh tail
    have hcode : out.firstcode[level]! = R.longcode := by
      have he := congrArg Prod.fst hprefix
      change out.firstcode = leaf.firstcode.set! (last + 1) codeSentinel at he
      rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega), firstPath_code_before tail (by omega)]
      change ready.firstcode[level]! = R.longcode
      unfold ready cheapCheck
      split
      all_goals rw [prepareFirst_code, Array.getElem!_set!_self _ _ _ (by
        have hh := hi.entry.1.codes; change st.firstcode.size = n + 2 at hh; omega)]
    have htarget : out.firsttc[level]! = Int.ofNat r.2.1.toNat := by
      have he := congrArg (fun r => r.2.1) hprefix
      change out.firsttc = leaf.firsttc.set! (last + 1) (-1) at he
      rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega), firstPath_before tail (by omega)]
      change ready.firsttc[level]! = Int.ofNat r.2.1.toNat
      unfold ready cheapCheck
      split
      all_goals rw [(prepareFirst_fields ctx tcLevel level numcells st).2.2,
        Array.getElem!_set!_self _ _ _ (by
          have hh := hi.entry.1.targets; change n < st.firsttc.size at hh; omega), hchoice]
      all_goals rfl
    exact ⟨r.2.1.toNat :: targets, ⟨R.longcode :: key.codes, key.rows⟩,
      .step hlt hcell hne ho ht href (fun h => (hb h).elim), hm'.cons hcode.symm htarget.symm⟩

end Hex.GraphIso.Nauty.Engine.Max
