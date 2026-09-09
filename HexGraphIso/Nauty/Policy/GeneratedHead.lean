/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.GeneratedTail
public import HexGraphIso.Nauty.Policy.FirstComplete
import all HexGraphIso.Nauty.Policy.GeneratedTail
import all HexGraphIso.Nauty.Policy.GeneratedCover
import all HexGraphIso.Nauty.Policy.GeneratedTrace
import all HexGraphIso.Nauty.Policy.FirstComplete
import all HexGraphIso.Nauty.Policy.FirstTail
import all HexGraphIso.Nauty.Policy.FirstWitness
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.MaxFirst
import all HexGraphIso.Nauty.Policy.MaxPosition
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxInit
import all HexGraphIso.Nauty.Policy.MaxNode
import all HexGraphIso.Nauty.Policy.MaxReturnTrace
import all HexGraphIso.Nauty.Policy.MaxReceive
import all HexGraphIso.Nauty.Policy.MaxResume
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.TraceContains
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Generation.Frame
import all HexGraphIso.Nauty.Generation.RefPath
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

set_option maxHeartbeats 1000000 in
/-- An internal actual first node covers the full orbit of its guiding
vertex in any final containing trace. Guiding return, reference transport,
and every suffix input are constructed from the node's actual path. -/
theorem firstPath_cover {G : Colored n k} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hp : Generic.FirstPath { g := rowsOf G } tcLevel fuel level numcells st last leaf)
    (hn : ∀ q, q < fuel → (contract G tcLevel).nodeValid q
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel q))
    {cs bs fs : List Nat} {parents : Parents n}
    (hi : NodeInput G { g := rowsOf G } tcLevel fuel true ⟨level, numcells, cs, st⟩ bs fs parents)
    {base : List (Fin n)} {gs : List (Perm n)}
    (hbase : ∀ b : Fin n, st.fixedpts.mem b.val = true ↔ b ∈ base)
    (htrace : Generation.Realizes G gs
      (Nauty.node true { g := rowsOf G } (n + 2) tcLevel fuel level numcells st).2.genTrace.toList)
    (hopen : (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 ≠ n) :
    ∃ guide : Fin n,
      guide.val = (((Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).2.2.1.nextElem none).getD 0) ∧
      ∀ v, Aut.Orbit G base guide v → Generation.Carries G gs base guide v := by
  cases hp with
  | leaf fuel level numcells st hdisc => exact (hopen hdisc).elim
  | @step fuel level numcells last st leaf tv hopen htv horbit tail =>
    let ctx : Ctx n := { g := rowsOf G }
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let R := st.refined ctx level numcells
    let l : Loop n := ⟨⟨level, numcells, cs, st⟩, true⟩
    let ready := cheapCheck true level r.2.2.2.2
    let ch := child true level r.2.1.toNat tv ready
    let raw := Nauty.node true ctx (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch
    let left := { afterChildFirst level tv raw.2 with fixedpts := raw.2.fixedpts.erase tv }
    let restored := recoverLevels level (recoverPtn (n + 2) level left)
    let parent : Parent n := ⟨l, ready, tv, bs, fs⟩
    have hp : Generic.FirstPath ctx tcLevel (fuel + 1) level numcells st last leaf :=
      .step hopen htv horbit tail
    have htv' : r.2.2.1.nextElem none = some tv := htv
    have hn0 : 0 < n := by have := hi.frame.positive; have := hi.frame.depth; omega
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
    have hret : raw.1 = .unwind level false := by
      simpa only [raw, ch, ready, r, ctx, policy, Generic.Policy.child, Generic.Policy.cheapCheck, Nat.add_sub_cancel] using firstPath_returns tail (fun f hf => hn f (by omega)) hc
    have hcall : Nauty.node (true && tv == tv) ctx (n + 2) tcLevel fuel
        (level + 1) (r.1 + 1) (child true level r.2.1.toNat tv ready) =
          (.unwind level false, raw.2) := by
      simp only [Bool.true_and, beq_self_eq_true]
      exact Prod.ext hret rfl
    have hv : (!true || ready.orbits[tv]! == tv) = true := by
      change ready.orbits[tv]! = tv at horbit
      simp only [Bool.not_true, Bool.false_or, beq_iff_eq]
      exact horbit
    obtain ⟨hgen, hanc⟩ := hs.received_generators (hn fuel (Nat.lt_succ_self _)) hcall
    obtain ⟨bs', fs', hs', _, _⟩ := hs.received_input (hn fuel (Nat.lt_succ_self _)) hv hcall hgen hanc
    simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      Bool.not_true, Bool.false_and] at hs'
    change SweepInput G ctx tcLevel fuel n true level r.1 r.2.1.toNat tv
      (r.2.2.1.nextElem (some tv)) r.2.2.1
      (if restored.orbits[tv]! == tv then 0 + 1 else 0) restored l bs' fs' parents at hs'
    have hit := refined_iter (ctx := ctx) hn0 hi.frame.positive hi.frame.partition
    have hfields := l.prepare_frame ctx tcLevel
    change r.1 = R.numcells ∧ ready.lab = R.lab ∧ ready.ptn = R.ptn at hfields
    obtain ⟨e, o, hlt, hcell, hne, ho, hat⟩ :=
      firstChild_offset hn0 hi.frame.positive hi.frame.partition htv
    change level < n at hlt
    change (r.2.1.toNat, e) ∈ cells R.ptn level n at hcell
    change r.2.1.toNat < e at hne
    change o ≤ e - r.2.1.toNat at ho
    change R.lab[r.2.1.toNat + o]! = tv at hat
    have hchoice := prepareFirst_choice hopen hit hi.entry.1.equitable
    have ht : r.2.1.toNat = specTargetcell ctx R.lab R.ptn level tcLevel := by rw [hchoice]; rfl
    obtain ⟨targets, key, href, hm⟩ := firstPath_witness tail (fun q hq => hn q (by omega)) hc
    change Nauty.Generation.RefPath ctx tcLevel raw.2.allsamelevel (level + 1)
      (ch.refined ctx (level + 1) (r.1 + 1)) targets key at href
    change Nauty.Generation.Matches ctx (level + 1) raw.2 targets key at hm
    have hrefChild := href
    rw [firstChild_refined, ← hat] at hrefChild
    have hleaf : Nauty.Generation.HasLeaf ctx tcLevel level R (r.2.1.toNat :: targets)
        ⟨R.longcode :: key.codes, key.rows⟩ := hrefChild.occurs.step hlt hcell hne ho ht
    have hprefix := firstPath_reference (inf := n + 2) tail
    have hl : level + 1 ≤ last := by
      have hh : ∀ {f l nc z : Nat} {s q : Search n}, Generic.FirstPath ctx tcLevel f l nc s z q → l ≤ z := by
        intro f l nc z s q hp
        induction hp with
        | leaf => exact Nat.le_refl _
        | step _ _ _ _ ih => omega
      exact hh tail
    have hcode : raw.2.firstcode[level]! = R.longcode := by
      have he := congrArg Prod.fst hprefix
      change raw.2.firstcode = leaf.firstcode.set! (last + 1) codeSentinel at he
      rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega), firstPath_code_before tail (by omega)]
      change ready.firstcode[level]! = R.longcode
      unfold ready cheapCheck
      split
      all_goals rw [prepareFirst_code, Array.getElem!_set!_self _ _ _ (by
        have hh := hi.entry.1.codes; change st.firstcode.size = n + 2 at hh; omega)]
    have htarget : raw.2.firsttc[level]! = Int.ofNat r.2.1.toNat := by
      have he := congrArg (fun r => r.2.1) hprefix
      change raw.2.firsttc = leaf.firsttc.set! (last + 1) (-1) at he
      rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega), firstPath_before tail (by omega)]
      change ready.firsttc[level]! = Int.ofNat r.2.1.toNat
      unfold ready cheapCheck
      split
      all_goals rw [(prepareFirst_fields ctx tcLevel level numcells st).2.2,
        Array.getElem!_set!_self _ _ _ (by
          have hh := hi.entry.1.targets; change n < st.firsttc.size at hh; omega), hchoice]
      all_goals rfl
    have hr : restored.reference = raw.2.reference := (referencePolicy ctx (n + 2) tcLevel).recover level left
    have hm' := matches_reference (hm.cons hcode.symm htarget.symm) hr
    have hfloor := firstPath_floor (inf := n + 2) tail
    change level + 1 ≤ raw.2.allsamelevel ∧ level + 1 ≤ raw.2.eqlevFirst at hfloor
    have hsame : raw.2.allsamelevel ≤ restored.allsamelevel := by rw [recover_same]; exact Nat.le_refl _
    have heq : restored.eqlevFirst = level := by
      rw [recover_eqlev]
      change min raw.2.eqlevFirst level = level
      exact Nat.min_eq_right (by omega)
    have hg : restored.gcaFirst = level := (gcaPolicy ctx (n + 2) tcLevel).recover level left
    have hpast : Generic.Past true tv (r.2.2.1.nextElem (some tv)) := by
      intro _ v hv
      have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
      change tv + 1 ≤ v at hh
      omega
    have hbaseReady : ∀ b : Fin n, ready.fixedpts.mem b.val = true ↔ b ∈ base := by
      intro b
      have he : ready.fixedpts = st.fixedpts := by
        unfold ready cheapCheck
        split
        all_goals change r.2.2.2.2.fixedpts = st.fixedpts
        all_goals dsimp only [r, Generic.prepareFirst]
        all_goals change (chooseTarget true ctx tcLevel level _ _).2.2.2.fixedpts = st.fixedpts
        all_goals rw [chooseFirst_fields]
        all_goals rfl
      rw [he]
      exact hbase b
    let guide : Fin n := ⟨tv, VSet.mem_lt (VSet.nextElem_mem htv')⟩
    refine ⟨guide, by rw [htv']; rfl, ?_⟩
    have hpos : restored.firstlab[r.2.1.toNat]! = guide.val := by
      have he := firstPath_frame tail hn0 hc.frame.positive hc.frame.partition
      have hpick := parent.picked hs.suspend
      have hh := congrArg (fun r => r.2.2) hprefix
      change raw.2.firstlab = leaf.lab at hh
      have he' : restored.firstlab = raw.2.firstlab := congrArg (fun r => r.2.2) hr
      rw [he', hh]
      exact (he.atSingleton hpick.1).trans hpick.2
    have hmove : ∀ v : Fin n, Aut.Orbit G base guide v → ∀ j,
        j < (l.prepare ctx tcLevel).2.2.2.1 → R.lab[r.2.1.toNat + j]! = v.val →
        Nauty.Generation.ChildPath ctx tcLevel raw.2.allsamelevel level R r.2.1.toNat targets key j := by
      intro v hv j hj hjv
      have hlen : (l.prepare ctx tcLevel).2.2.2.1 = e + 1 - r.2.1.toNat := by
        have hc := cells_isCell (Nat.le_of_eq hit.ok.ptnSize.symm) hit.ok.ptnEnd _ hcell
        have hsCell := hs.window
        change IsCell ready.ptn level r.2.1.toNat (l.prepare ctx tcLevel).2.2.2.1 at hsCell
        rw [hfields.2.2] at hsCell
        rcases isCell_disjoint_or_eq hc hsCell with he | he | he <;> omega
      exact hrefChild.orbit hit hlt hs.path.stab hfields.2.1 hfields.2.2
        (fun b hb => (hbaseReady b).mp hb) hcell hne ho (by rw [hlen] at hj; omega)
        hat hjv hv
    have hfixFrame : ∀ γ, CellStab R.ptn level R.lab γ → ∀ b ∈ base, γ[b.val]! = b.val := by
      intro γ hγ
      apply Nauty.Generation.frame_fixes hs.path.fixed hs.partition.labSize
        (fun b hb => (hbaseReady b).mpr hb)
      change CellStab ready.ptn level ready.lab γ
      rwa [hfields.2.1, hfields.2.2]
    have hwindow : Generation.Cover G gs base guide r.2.2.1 none := by
      apply Generation.Cover.start
      intro v hv
      obtain ⟨p, hp, hfix, rfl⟩ := hv
      have hcellEq : r.2.2.1 = windowSet n ready.lab r.2.1.toNat (l.prepare ctx tcLevel).2.2.2.1 := by
        have hnum : (l.prepare ctx tcLevel).1 < n := by
          change r.1 < n
          have hh := hs.partition.count
          change r.1 = bcount ready.ptn level n at hh
          have hb := bcount_le ready.ptn level n
          change r.1 ≠ n at hopen
          omega
        have hh := l.first_shape hi.frame rfl hnum
        exact hh.2.2.2
      rw [hcellEq]
      apply Nauty.Generation.window_stable hs.path.stab (labOk_of_reach hs.partition.labSize hs.partition.reach)
        hs.window (by rw [hs.partition.labSize]; exact hs.range) hp
        (fun b hb => hfix b ((hbaseReady b).mp hb)) guide
      change (windowSet n ready.lab r.2.1.toNat (l.prepare ctx tcLevel).2.2.2.1).mem guide.val = true
      rw [← hcellEq]
      exact VSet.nextElem_mem htv'
    have hcover := hwindow.advance (tv := guide) htv' (fun _ => Generation.Carries.refl G gs base guide)
    have hcanon := hs.canon_past (Nauty.Generation.CanonPast.start (by
      have hh := hi.entry.2.2.2.2.2.2.2.2.2
      change ready.gcaCanon < level
      have hg := (l.ancestors ctx tcLevel).2
      change ready.gcaCanon = st.gcaCanon at hg
      rw [hg]
      exact hh)) htv'
    rw [hcall] at hcanon
    simp only [Bool.true_and, beq_self_eq_true, ↓reduceIte] at hcanon
    have htraceLoop : Generation.Realizes G gs (Nauty.sweep true ctx (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 ready).2.2.genTrace.toList := by
      apply htrace.mono
      intro γ hγ
      rw [node_first]
      simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ↓reduceIte, htv, Option.getD_some]
      generalize hx : Nauty.sweep true ctx (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 ready = result at hγ ⊢
      obtain ⟨exit, index, result⟩ := result
      cases exit <;> dsimp only
      · unfold afterSweep
        split <;> exact hγ
      · exact hγ
      · exact hγ
    have hstep := (hs.receive_call (hn fuel (Nat.lt_succ_self _)) hv hcall
      (Generic.sweepCall ctx (n + 2) tcLevel fuel n)).1
    unfold Generic.nodeCall Generic.sweepCall at hstep
    rw [sweep_eq_generic, Generic.sweep, hstep] at htraceLoop
    simp only [← sweep_eq_generic, Bool.true_and, beq_self_eq_true, Bool.not_true,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte] at htraceLoop
    apply hs'.generated_tail (fun q hq => hn q (by omega)) hpast hit
      hfields.2.1.symm hfields.2.2.symm (show R.numcells = r.1 from rfl)
      hleaf hm' hg heq (by omega) hsame hmove hfixFrame rfl hcanon hcover hpos
    dsimp only [restored, left, afterChildFirst] at htraceLoop ⊢
    exact htraceLoop

end Hex.GraphIso.Nauty.Max
