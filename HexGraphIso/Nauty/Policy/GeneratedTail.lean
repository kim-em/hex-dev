/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.GeneratedReceipt
public import HexGraphIso.Nauty.Policy.ReferenceComplete
public import HexGraphIso.Nauty.Policy.FirstTail
import all HexGraphIso.Nauty.Policy.GeneratedReceipt
import all HexGraphIso.Nauty.Policy.GeneratedTrace
import all HexGraphIso.Nauty.Policy.GeneratedCover
import all HexGraphIso.Nauty.Policy.ReferenceComplete
import all HexGraphIso.Nauty.Policy.ReferenceSweep
import all HexGraphIso.Nauty.Policy.ReferenceReturn
import all HexGraphIso.Nauty.Policy.TraceContains
import all HexGraphIso.Nauty.Policy.FirstTail
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.FirstWitness
import all HexGraphIso.Nauty.Policy.MaxReturnTrace
import all HexGraphIso.Nauty.Policy.MaxResume
import all HexGraphIso.Nauty.Policy.MaxReceive
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxSkip
import all HexGraphIso.Nauty.Policy.Coset
import all HexGraphIso.Nauty.Policy.EarlyReturn
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- The actual first-path sibling suffix covers the guide's full orbit
by generators in any final containing trace. Every received reference is
proved by the smaller node call, and every skip uses a recorded word. -/
theorem SweepInput.generated_tail {G : Colored n k} {tcLevel fuel cfuel boundary : Nat}
    {level numcells tc tv1 index : Nat} {cursor : Option Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel true level numcells tc tv1 cursor
      cell index st l bs fs parents)
    (hn : ∀ q, q ≤ fuel → (contract G tcLevel).nodeValid q
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel q))
    (hpast : Generic.Past true tv1 cursor)
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk { g := rowsOf G } level R)
    (hlab : R.lab = (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.ptn) (hnc : R.numcells = numcells)
    (hleaf : Nauty.Generation.HasLeaf { g := rowsOf G } tcLevel level R (tc :: targets)
      ⟨R.longcode :: key.codes, key.rows⟩)
    (hm : Nauty.Generation.Matches { g := rowsOf G } level st.view (tc :: targets)
      ⟨R.longcode :: key.codes, key.rows⟩)
    (hg : st.gcaFirst = level) (heq : st.eqlevFirst = level)
    (hboundary : level < boundary) (hsame : boundary ≤ st.allsamelevel)
    {gs : List (Perm n)} {base : List (Fin n)} {guide : Fin n}
    (hmove : ∀ v : Fin n, Aut.Orbit G base guide v → ∀ o,
      o < (l.prepare { g := rowsOf G } tcLevel).2.2.2.1 → R.lab[tc + o]! = v.val →
      Nauty.Generation.ChildPath { g := rowsOf G } tcLevel boundary level R tc targets key o)
    (hfixFrame : ∀ γ, CellStab R.ptn level R.lab γ → ∀ b ∈ base, γ[b.val]! = b.val)
    {previous : Option Nat} (hnext : cell.nextElem previous = cursor)
    (hcanon : Nauty.Generation.CanonPast level tc previous st.view)
    (hcover : Generation.Cover G gs base guide cell previous)
    (hfirst : st.firstlab[tc]! = guide.val)
    (htrace : Generation.Realizes G gs
      (Engine.sweep true { g := rowsOf G } (n + 2) tcLevel fuel cfuel
        level numcells tc tv1 cursor cell index st).2.2.genTrace.toList) :
    ∀ v, Aut.Orbit G base guide v → Generation.Carries G gs base guide v := by
  induction cfuel generalizing cursor cell index st bs fs previous with
  | zero =>
    cases cursor with
    | none => exact hcover.finish hnext
    | some tv =>
      have hh := h.cursor_fuel tv rfl
      have ht := VSet.mem_lt (h.cursor_mem tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none => exact hcover.finish hnext
    | some tv =>
      let ctx : Ctx n := { g := rowsOf G }
      have htv := hpast rfl tv rfl
      have hf : (true && tv == tv1) = false := by
        simp only [Bool.true_and, beq_eq_false_iff_ne]; omega
      have hnextPast : ∀ cell : VSet n, Generic.Past true tv1 (cell.nextElem (some tv)) := by
        intro cell _ v hv
        have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hh
        omega
      let v : Fin n := ⟨tv, VSet.mem_lt (h.cursor_mem tv rfl)⟩
      by_cases hv : (!true || st.orbits[tv]! == tv) = true
      · obtain ⟨target, short, out, hcall⟩ := h.child_exit
          (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
        have he := congrArg Prod.fst hcall
        rw [hf] at he
        have ht := h.visit_level htv hit hlab hptn hnc hleaf hm hg heq (by omega)
          (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) he
        subst target
        have hsflag : short = false := by
          cases short with
          | false => rfl
          | true =>
            have hl : 0 < level := by rw [h.level_eq]; exact h.node.positive
            have hh := node_short_first hl he
            change level ≠ st.gcaFirst at hh
            exact (hh hg.symm).elim
        subst short
        let left := { out with fixedpts := out.fixedpts.erase tv }
        let ready := recoverLevels level (recoverPtn (n + 2) level left)
        let nextIndex := if ready.orbits[tv]! == tv1 then index + 1 else index
        have hc : Engine.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child true level tc tv st) = (.unwind level false, out) := by simpa only [hf] using hcall
        obtain ⟨hgen, hanc⟩ := h.received_generators (hn fuel (Nat.le_refl _)) hcall
        obtain ⟨bs', fs', hs, _, _⟩ := h.received_input (hn fuel (Nat.le_refl _)) hv hcall hgen hanc
        simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.true_and] at hs
        change SweepInput G ctx tcLevel fuel cfuel true level numcells tc tv1
          (cell.nextElem (some tv)) cell nextIndex ready l bs' fs' parents at hs
        have hstep := (h.receive_call (hn fuel (Nat.le_refl _)) hv hcall
          (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)).1
        unfold Generic.nodeCall Generic.sweepCall at hstep
        have hsweep : Engine.sweep true ctx (n + 2) tcLevel fuel (cfuel + 1)
            level numcells tc tv1 (some tv) cell index st =
            Engine.sweep true ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1
              (cell.nextElem (some tv)) cell nextIndex ready := by
          rw [sweep_eq_generic, Generic.sweep, hstep]
          simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_and, Bool.true_and]
          rw [← sweep_eq_generic]
        rw [hsweep] at htrace
        have htout : Generation.Realizes G gs out.genTrace.toList := by
          apply htrace.mono
          intro γ hγ
          have hmγ : γ ∈ ready.genTrace := by
            have hh := received_trace true (n + 2) level tv1 tv out
            simp only [hf, Bool.false_eq_true, ↓reduceIte] at hh
            rw [hh]
            simpa using hγ
          exact Array.mem_toList_iff.mpr (sweep_contains ctx (n + 2) tcLevel fuel cfuel true
            level numcells tc tv1 nextIndex _ cell ready (hnextPast cell) hmγ)
        have hfix : ∀ γ ∈ out.genTrace, ∀ b ∈ base, γ[b.val]! = b.val := by
          intro γ hγ
          apply hfixFrame γ
          rw [hlab, hptn]
          apply hs.generators rfl γ
          have hh := received_trace true (n + 2) level tv1 tv out
          simp only [hf, Bool.false_eq_true, ↓reduceIte] at hh
          rwa [hh]
        have hchild := h.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
        rw [hf] at hchild
        let ch : Frame n := ⟨level + 1, numcells + 1, l.codes ctx, child true level tc tv st⟩
        have hi : NodeInput G ctx tcLevel fuel false ch bs fs (parents.push ⟨l, st, tv, bs, fs⟩) := by
          simpa only [Parent.child, ← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] using hchild
        have hstored := hi.stored (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
        change RunInv G ctx (Engine.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
          (child true level tc tv st)).2 at hstored
        rw [hc] at hstored
        have hreference : out.reference = st.reference := by
          have hh := node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child true level tc tv st)
          rw [hc] at hh
          exact hh
        have hadv : Generation.Cover G gs base guide cell (some tv) := by
          by_cases horbit : Aut.Orbit G base guide v
          · obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp (mem_windowSet.mp
              (h.subset tv (h.cursor_mem tv rfl))).2
            change (l.prepare ctx tcLevel).2.2.2.2.lab[tc + o]! = tv at hat
            have href := h.reference_child hit hlab hptn hnc (size_rowsOf G) ho
              (by rw [hlab]; exact hat) (hmove v horbit o ho (by rw [hlab]; exact hat))
            have hr := reference_complete G tcLevel fuel ch bs fs (parents.push ⟨l, st, tv, bs, fs⟩)
              boundary targets key (fun q hq => hn q (by omega)) hi href
              (hm.tail.stateEq rfl rfl rfl) (by change st.eqlevFirst = level + 1 - 1; omega)
              hsame level false (congrArg Prod.fst hc)
            change RefReturn ctx level (Engine.node false ctx (n + 2) tcLevel fuel
              (level + 1) (numcells + 1) (child true level tc tv st)).2 at hr
            rw [hc] at hr
            apply hcover.receipt (tv := v) h hnext hcanon hc hr hstored.orbits htout hfix
            · have hh := congrArg (fun r => r.2.2) hreference
              change out.firstlab = st.firstlab at hh
              rw [hh]; exact hfirst
            · have hh := node_coset ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
                (child true level tc tv st)
              rw [hc] at hh
              exact hh
          · exact hcover.advance (tv := v) hnext (fun hv => (horbit hv).elim)
        have hr : ready.reference = st.reference :=
          ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hreference
        have heq' : ready.eqlevFirst = level := by
          have hh := Generic.node_bounded (firstFloor ctx (n + 2) tcLevel level)
            fuel (level + 1) (numcells + 1) (child true level tc tv st) (by omega)
            (show level ≤ st.allsamelevel ∧ level ≤ st.eqlevFirst from ⟨by omega, by omega⟩)
          rw [← node_eq_generic, hc] at hh
          rw [recover_eqlev]
          change min out.eqlevFirst level = level
          exact Nat.min_eq_right hh.2
        have hg' : ready.gcaFirst = level := by
          have hh := h.recovered_control
          rw [hcall] at hh
          simpa only [hf, Bool.false_eq_true, ↓reduceIte] using hh.1 rfl
        have hsame' : boundary ≤ ready.allsamelevel := by
          rw [recover_same]
          have hh := node_same ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child true level tc tv st)
          rw [hc] at hh
          change boundary ≤ out.allsamelevel
          rw [hh]
          exact hsame
        have hcanon' := h.canon_past hcanon hnext
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hcanon'
        rw [hc] at hcanon'
        have hfirst' : ready.firstlab[tc]! = guide.val := by
          have hh := congrArg (fun r => r.2.2) hr
          change ready.firstlab = st.firstlab at hh
          rw [hh]; exact hfirst
        exact ih hs (hnextPast cell) (matches_reference hm hr) hg' heq' hsame'
          rfl hcanon' hadv hfirst' htrace
      · have hskip : (!true || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hv
        have hs := h.skip_input (size_rowsOf G) hskip
        let nextIndex := if st.orbits[tv]! == tv1 then index + 1 else index
        have he : Engine.sweep true ctx (n + 2) tcLevel fuel (cfuel + 1)
            level numcells tc tv1 (some tv) cell index st =
            Engine.sweep true ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1
              (cell.nextElem (some tv)) cell nextIndex st := by
          rw [Engine.sweep]
          simp only [hskip, Bool.false_eq_true, ↓reduceIte, Id.run_pure, Bool.true_and]
          rfl
        rw [he] at htrace
        have hsttrace : Generation.Realizes G gs st.genTrace.toList := by
          apply htrace.mono
          intro γ hγ
          exact Array.mem_toList_iff.mpr (sweep_contains ctx (n + 2) tcLevel fuel cfuel true
            level numcells tc tv1 nextIndex _ cell st (hnextPast cell) (by simpa using hγ))
        have hadv := hcover.orbitSkip (tv := v) hnext (h.skip_phase hskip).2.1.stored.orbits
          hsttrace (fun γ hγ => hfixFrame γ (by rw [hlab, hptn]; exact h.generators rfl γ (by simpa using hγ)))
          (by simpa only [Bool.not_true, Bool.false_or, beq_eq_false_iff_ne] using hskip)
        exact ih hs (hnextPast cell) hm hg heq hsame rfl
          (hcanon.advance (nextElem_after hnext)) hadv hfirst htrace

end Hex.GraphIso.Nauty.Engine.Max
