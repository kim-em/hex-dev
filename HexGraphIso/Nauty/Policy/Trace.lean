/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Alignment
public import HexGraphIso.Nauty.Policy.Scratch
public import HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Every permutation in the unbounded generator trace is a checked automorphism. -/
def TraceOk (ctx : Ctx n) (st : Search n) : Prop :=
  ∀ γ ∈ st.genTrace, checkAutom ctx.g γ = true

/-- Classification builds scratch data without adding it to the generator trace. -/
theorem classify_trace (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.genTrace = st.genTrace := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.genTrace, ite_self]

private theorem pruneReturn_trace (level : Nat) (st : Search n) :
    (pruneReturn level st).2.genTrace = st.genTrace := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite Search.genTrace, pushAuto_trace, ite_self]

/-- An internal classification returns the input state unchanged. -/
theorem classify_internal_state {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (h : (classify ctx level numcells st).1 = .internal) :
    classify ctx level numcells st = (.internal, st) := by
  obtain ⟨hguard, hnc⟩ := (classify_internal ctx level numcells st).mp h
  have hg : ¬ (st.eqlevFirst != level && decide (st.compCanon < 0)) = true := by
    simpa only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] using hguard
  unfold classify
  simp only [hg, Bool.false_eq_true, ite_false, bne_iff_ne.mpr hnc, ite_true, Id.run_pure]

/-- The two automorphism verdicts append exactly the scratch permutation. -/
theorem leafExit_trace (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.genTrace =
      match leaf with
      | .autoFirst | .autoCanon => st.genTrace.push st.workperm
      | _ => st.genTrace := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite Search.genTrace, admit_trace, pruneReturn_trace, ite_self,
    install]

/-- Only the two automorphism verdicts append a permutation. Both require a checked scratch value. -/
theorem leafExit_checked {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : TraceOk ctx st) (leaf : Leaf)
    (hcheck : leaf = .autoFirst ∨ leaf = .autoCanon → checkAutom ctx.g st.workperm = true) :
    TraceOk ctx (leafExit leaf level st).2 := by
  intro γ hγ
  cases leaf with
  | autoFirst =>
    rw [leafExit_trace, Array.mem_push] at hγ
    exact hγ.elim (h γ) (fun heq => heq ▸ hcheck (Or.inl rfl))
  | autoCanon =>
    rw [leafExit_trace, Array.mem_push] at hγ
    exact hγ.elim (h γ) (fun heq => heq ▸ hcheck (Or.inr rfl))
  | internal => exact h γ hγ
  | better sr => rw [leafExit_trace] at hγ; exact h γ hγ
  | bad => rw [leafExit_trace] at hγ; exact h γ hγ

/-- At a discrete node, alignment supplies the two histories required by cheap admission. -/
theorem Aligned.first_checked {G : Colored n k} {ctx : Ctx n} {tcLevel level numcells : Nat}
    {root : RefineSt n} {st out : Search n}
    (h : Aligned ctx st.gcaFirst root level level numcells st)
    (href : FirstRef ctx tcLevel st.gcaFirst root st) (hdepth : Depth href.last st)
    (hsmall : SubtreeOk ctx st.gcaFirst root)
    (hok : SearchOk G level numcells st)
    (hauto : Nauty.classify ctx level numcells st = (.autoFirst, out))
    (hwork : st.workperm.size = n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    checkAutom ctx.g out.workperm = true := by
  obtain ⟨hnc, heq, _, _⟩ := classify_first hauto
  obtain ⟨current, hh, hl, hp, hc⟩ := h.descent heq
  have hbound : level ≤ href.last := by rw [← heq]; exact hdepth.1
  have hdisc : ∀ i, i < n → current.ptn[i]! ≤ level := by
    have hcount := hok.count
    change numcells = bcount st.ptn level n at hcount
    rw [hnc] at hcount
    have hall : (List.range n).countP (fun i => decide (st.ptn[i]! ≤ level)) =
        (List.range n).length := by
      simpa only [bcount, List.length_range] using hcount.symm
    intro i hi
    rw [hp]
    exact of_decide_eq_true (List.countP_eq_length.mp hall i (List.mem_range.mpr hi))
  obtain ⟨_, _, hout, _⟩ := classify_first hauto
  rw [hout]
  exact href.scatter hbound hgsz hsymm hloop hsmall hh hdisc hl.symm hwork

/-- A code-one admission outside a cheap ancestor is justified by its explicit scan. -/
theorem classify_first_scanned {ctx : Ctx n} {level numcells : Nat} {st out : Search n}
    (hauto : Nauty.classify ctx level numcells st = (.autoFirst, out))
    (hnoncheap : st.gcaFirst < st.noncheaplevel)
    (hwork : st.workperm.size = n)
    (hfirst : st.firstlab.size = n) (hfirstPerm : st.firstlab.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n))
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    checkAutom ctx.g out.workperm = true := by
  obtain ⟨_, _, hout, hguard⟩ := classify_first hauto
  have hscan := hguard.resolve_left (by omega)
  rw [hout] at hscan ⊢
  exact scatter_isautom hwork hfirst hfirstPerm hlab hlabPerm hsymm hloop hscan

end Hex.GraphIso.Nauty
