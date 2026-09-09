/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ReferenceNode
import all HexGraphIso.Nauty.Policy.ReferenceNode
import all HexGraphIso.Nauty.Policy.ReferenceLoop
import all HexGraphIso.Nauty.Policy.ReferenceDescent
import all HexGraphIso.Nauty.Policy.ReferenceSweep
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
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- A valid actual off-path node containing the stored reference returns
emitted evidence. The only recursive premises are smaller maximum calls;
reference descent and its receiving sweeps are proved here. -/
theorem reference_complete (G : Colored n k) (tcLevel : Nat) :
    ∀ fuel (f : Frame n) bs fs parents boundary targets key,
      (∀ q, q < fuel → (contract G tcLevel).nodeValid q
        (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel q)) →
      NodeInput G { g := rowsOf G } tcLevel fuel false f bs fs parents →
      Generation.RefPath { g := rowsOf G } tcLevel boundary f.level
        (f.entry.refined { g := rowsOf G } f.level f.numcells) targets key →
      Generation.Matches { g := rowsOf G } f.level f.entry targets key →
      f.entry.eqlevFirst = f.level - 1 → boundary ≤ f.entry.allsamelevel →
      ∀ target short,
        (Nauty.node false { g := rowsOf G } (n + 2) tcLevel fuel f.level f.numcells f.entry).1 =
          .unwind target short →
        RefReturn { g := rowsOf G } target
          (Nauty.node false { g := rowsOf G } (n + 2) tcLevel fuel f.level f.numcells f.entry).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro f bs fs parents boundary targets key hn h
    have := h.fuel
    have := h.frame.depth
    omega
  | succ fuel ih =>
    intro f bs fs parents boundary targets key hn h href hm heq hsame target short hret
    let ctx : Ctx n := { g := rowsOf G }
    let rs := f.entry.refined ctx f.level f.numcells
    have ht := h.reference_tree
    change Generation.TreeOk ctx f.level rs at ht
    have hi := h.entry.1.stored
    have hg := h.entry.1.ancestor
    have hbudget : n < f.level + (fuel + 1) := by have := h.fuel; omega
    have hfirst :
        ((Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).1 =
          .unwind f.entry.gcaFirst false ∧
          LabelCarrier ctx f.entry.firstlab
            (Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2.lab
            (Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2.genTrace) →
        RefReturn ctx target
          (Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2 := by
      intro hh
      rw [hret] at hh
      cases hh.1
      apply RefReturn.first
      · rw [node_gca]
      · have hr := node_reference ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry
        have hl := congrArg (fun r => r.2.2) hr
        change (Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2.firstlab = f.entry.firstlab at hl
        rw [hl]
        exact hh.2
    have emit : Generation.Uniform ctx tcLevel f.level rs targets key →
        RefReturn ctx target
          (Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2 := by
      intro hu
      exact hfirst (uniform_reference (size_rowsOf G) (rowsOf_symm G) ht hu
        hi.scratch hi.firstSize hi.first hm heq hg hbudget)
    by_cases hb : boundary ≤ f.level
    · exact emit (href.uniform ht.it hb)
    have hleaf := href.occurs
    cases href with
    | leaf hd => exact emit (Generation.Uniform.leaf ht.it hd)
    | @step _ tc e o _ rest tail hlvl hcell hne ho htarget hchild hu =>
      by_cases hc : cheapautom rs.ptn f.level n = true
      · exact hfirst (cheap_reference (n + 2) tcLevel (size_rowsOf G) (rowsOf_symm G)
          (rowsOf_loopless G) (fuel + 1) f.level f.numcells f.entry _ _
          (subtreeOk_of_cheapautom ht.it ht.eqt ht.acc hc) hi.scratch hi.firstSize hi.first
          hm hleaf heq hg hbudget)
      have hend := target_end_lt ht.it.ok.ptnSize ht.it.ok.ptnEnd hcell
      have hic : IsCell rs.ptn f.level tc (e + 1 - tc) :=
        cells_isCell (by rw [ht.it.ok.ptnSize]; exact Nat.le_refl _) ht.it.ok.ptnEnd _ hcell
      have hnc : rs.numcells < n := by
        have hle := ht.acc ▸ bcount_le rs.ptn f.level n
        by_cases he : rs.numcells = n
        · have ha : List.countP (fun q => decide (rs.ptn[q]! ≤ f.level)) (List.range n) =
              (List.range n).length := by rw [List.length_range]; exact ht.acc.trans he
          have hclosed := List.countP_eq_length.mp ha tc (List.mem_range.mpr (by omega))
          have hopen := hic.2.2.1 tc (Nat.le_refl _) (by omega)
          simp only [decide_eq_true_eq] at hclosed
          omega
        · omega
      let l : Loop n := ⟨f, false⟩
      let p := l.prepare ctx tcLevel
      have hprep := Loop.reference_prepare ht hm hleaf heq hnc
      change (let q := prepareOther ctx tcLevel f.level f.numcells f.entry;
        (classify ctx f.level q.1 q.2.2.2.2.2).1 = .internal) ∧ _ at hprep
      have hclass := hprep.1
      have hs := h.other_input (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hclass
      have hce : cellEnd rs.ptn f.level (tc + 1) = tc + (e + 1 - tc) - 1 :=
        cellEnd_of_isCell hic (by omega) (by rw [ht.it.ok.ptnSize]; omega)
      have hmt : specMaketargetcell ctx rs.lab rs.ptn f.level tcLevel =
          (tc, windowSet n rs.lab tc (e + 1 - tc), e + 1 - tc) := by
        rw [specMaketargetcell, ← htarget, hce,
          worksetOf_eq_windowSet _ tc (e + 1 - tc) (by omega)]
        congr 2 <;> omega
      change (let q := prepareOther ctx tcLevel f.level f.numcells f.entry;
        (classify ctx f.level q.1 q.2.2.2.2.2).1 = .internal) ∧
        p.2.1 = Int.ofNat (specMaketargetcell ctx rs.lab rs.ptn f.level tcLevel).1 ∧ _ at hprep
      rw [hmt] at hprep
      dsimp only at hprep
      obtain ⟨_, htc, hset, hlen, heqPrep, hrefPrep, hsamePrep, hgPrep, hcanonPrep⟩ := hprep
      have htc' : p.2.1.toNat = tc := by rw [htc]; rfl
      change SweepInput G ctx tcLevel fuel (n + 1) false f.level p.1 p.2.1.toNat
        ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
        l bs fs parents at hs
      rw [htc'] at hs
      have hframes := l.prepare_frame ctx tcLevel
      change p.1 = rs.numcells ∧ p.2.2.2.2.lab = rs.lab ∧ p.2.2.2.2.ptn = rs.ptn at hframes
      have hloop := hs.reference (boundary := boundary) (targets := rest) (key := tail) (hn fuel (by omega)) ht.it hframes.2.1.symm hframes.2.2.symm (by omega)
      have hc' : cheapautom p.2.2.2.2.ptn f.level n = false := by
        rw [hframes.2.2]
        exact Bool.eq_false_iff.mpr hc
      have hpark : f.level < p.2.2.2.2.noncheaplevel := by
        dsimp only [p, Loop.prepare, l]
        unfold cheapCheck
        have hptn : (chooseTarget false ctx tcLevel f.level
            (Nauty.visit ctx f.level f.numcells f.entry).1
            (compareCodes f.level (Nauty.visit ctx f.level f.numcells f.entry).2.1
              (Nauty.visit ctx f.level f.numcells f.entry).2.2)).2.2.2.ptn = rs.ptn := by
          rw [chooseTarget_fields, (compareCodes_frame ..).2.1]
          rfl
        simp only [Bool.false_eq_true, ↓reduceIte, hptn,
          Bool.eq_false_iff.mpr hc, Bool.not_false, Bool.true_or, Bool.and_self]
        omega
      have hvisit : ∀ {cfuel tv index cell st bs fs},
          SweepInput G ctx tcLevel fuel cfuel false f.level p.1 tc
            ((p.2.2.1.nextElem none).getD 0) (some tv) cell index st l bs fs parents →
          Generation.Matches ctx (f.level + 1) st rest tail → st.eqlevFirst = f.level →
          boundary ≤ st.allsamelevel → st.gcaFirst < f.level →
          ∀ j, j < (l.prepare ctx tcLevel).2.2.2.1 → rs.lab[tc + j]! = tv →
          Generation.ChildPath ctx tcLevel boundary f.level rs tc rest tail j →
          let out := Nauty.node false ctx (n + 2) tcLevel fuel (f.level + 1) (p.1 + 1)
            (child false f.level tc tv st)
          ∀ target short, out.1 = .unwind target short → RefReturn ctx target out.2 := by
        intro cfuel tv index cell st bs fs hh hmatch heq' hsame' hg' j hj hat hp
        have hi := hh.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
        have href := hh.reference_child ht.it hframes.2.1.symm hframes.2.2.symm hframes.1.symm
          (size_rowsOf G) hj hat hp
        let ch : Frame n := ⟨f.level + 1, p.1 + 1, l.codes ctx, child false f.level tc tv st⟩
        have hie : NodeInput G ctx tcLevel fuel false ch bs fs
            (parents.push ⟨l, st, tv, bs, fs⟩) := by
          simpa only [Parent.child, ← hh.first_eq, ← hh.level_eq, ← hh.numcells_eq, ← hh.tc_eq,
            Bool.false_and] using hi
        exact ih ch bs fs (parents.push ⟨l, st, tv, bs, fs⟩) boundary rest tail
          (fun q hq => hn q (by omega)) hie href (hmatch.stateEq rfl rfl rfl)
          (by change st.eqlevFirst = f.level + 1 - 1; omega) hsame'
      have hcover : Generation.PathCover ctx tcLevel boundary f.level rs tc
          (l.prepare ctx tcLevel).2.2.2.1 rest tail p.2.2.1 none := by
        rw [hset, hlen]
        apply Generation.PathCover.start
        intro j hj
        exact ht.it.ok.labOk _ (by rw [ht.it.ok.labSize]; omega)
      have hocc : ∃ j, j < (l.prepare ctx tcLevel).2.2.2.1 ∧
          Generation.ChildPath ctx tcLevel boundary f.level rs tc rest tail j := by
        refine ⟨o, ?_, hchild⟩
        change o < p.2.2.2.1
        rw [hlen]
        omega
      have hpast : Generation.CanonPast f.level tc none p.2.2.2.2 := by
        apply Generation.CanonPast.start
        change p.2.2.2.2.gcaCanon < f.level
        rw [hcanonPrep]
        exact h.entry.1.canonAncestor
      obtain ⟨t, s, result, hrun, _, hr⟩ := hloop hvisit rfl hcover hocc hpast
        (matches_reference hm.tail hrefPrep) heqPrep (by rw [hsamePrep]; exact hsame)
        (by rw [hgPrep]; exact hg) hpark
      have hstep := l.node_step (Generic.sweepCall ctx (n + 2) tcLevel fuel (n + 1))
        (fun he => by cases he) (fun _ => hclass)
      unfold Generic.sweepCall at hstep
      change (Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).1 = _ at hret
      have he : Nauty.node false ctx (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry =
          (.unwind t s, result.2) := by
        rw [node_eq_generic, Generic.node, hstep]
        change (match (Generic.sweep false ctx (n + 2) tcLevel fuel (n + 1) f.level p.1
          p.2.1.toNat ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2).1 with
          | .done => _ | _ => _) = _
        rw [← sweep_eq_generic, htc', hrun]
      rw [he] at hret ⊢
      cases hret
      exact hr

end Hex.GraphIso.Nauty.Max
