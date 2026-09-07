/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Search.Engine
import all HexGraphIso.Nauty.Policy.State

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

private def canonVerdict (ctx : Ctx n) (level : Nat) (st : Search n) : Leaf × Search n := Id.run do
  let mut st := st
  let mut sr := 0
  if st.compCanon == 0 then
    if level < st.canonlevel then
      st := { st with compCanon := 1 }
    else
      st := { st with canong := updatecan ctx st.canong st.canonlab st.samerows, samerows := n }
      let (c, s) := testcanlab ctx st.canong st.lab
      st := { st with compCanon := c }
      sr := s
  if st.compCanon == 0 then
    return (.autoCanon, scatter st.canonlab st)
  else if st.compCanon > 0 then
    return (.better sr, st)
  else
    return (.bad, st)

private theorem canonVerdict_ne (ctx : Ctx n) (level : Nat) (st : Search n) :
    (canonVerdict ctx level st).1 ≠ .autoFirst := by
  unfold canonVerdict
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst]
  repeat' split
  all_goals intro h; cases h

private theorem classify_eq (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    classify ctx level numcells st =
      if st.eqlevFirst != level && st.compCanon < 0 then (.bad, st)
      else if numcells != n then (.internal, st)
      else if st.eqlevFirst == level then
        let sc := scatter st.firstlab st
        if sc.gcaFirst >= sc.noncheaplevel || isautom ctx sc.workperm then (.autoFirst, sc)
        else canonVerdict ctx level sc
      else canonVerdict ctx level st := by
  rfl

private theorem canonVerdict_checked {ctx : Ctx n} {level : Nat} {st out : Search n}
    (hauto : canonVerdict ctx level st = (.autoCanon, out))
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows)
    (hwork : st.workperm.size = n)
    (href : st.canonlab.size = n) (hrefPerm : st.canonlab.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n)) :
    checkAutom ctx.g out.workperm = true := by
  by_cases hcomp : st.compCanon = 0
  · by_cases hlevel : level < st.canonlevel
    · simp [canonVerdict, hcomp, hlevel] at hauto
    · have hrows : (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0 →
          leafRows ctx st.canonlab = leafRows ctx st.lab :=
        rows_eq_of_testcanlab_tie (st := st.view) hinv
      simp only [canonVerdict, hcomp, beq_self_eq_true, ite_true, hlevel, ite_false] at hauto
      split at hauto
      · rename_i htie
        have hchecked := scatter_checked hwork href hrefPerm hlab hlabPerm
          (hrows (by simpa using htie))
        have hout := (Prod.mk.inj hauto).2
        rw [← hout]
        rw [scatter_eq] at hchecked ⊢
        exact hchecked
      · split at hauto <;> cases hauto
  · simp only [canonVerdict, beq_eq_false_iff_ne.mpr hcomp, Bool.false_eq_true, ite_false] at hauto
    split at hauto <;> cases hauto

/-- The current canonical store is valid, and a better verdict carries
the row-prefix invariant needed to install the candidate. -/
def VerdictInv (ctx : Ctx n) (r : Leaf × Search n) : Prop :=
  CanongInv ctx r.2.canong r.2.canonlab r.2.samerows ∧
    ∀ sr, r.1 = .better sr → CanongInv ctx r.2.canong r.2.lab sr

private theorem verdict_store (ctx : Ctx n) (sr : Nat) (st : Search n)
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows)
    (hnew : CanongInv ctx st.canong st.lab sr) :
    VerdictInv ctx (if st.compCanon == 0 then (.autoCanon, scatter st.canonlab st)
      else if st.compCanon > 0 then (.better sr, st) else (.bad, st)) := by
  split
  · refine ⟨?_, fun _ h => by cases h⟩
    simpa only [scatter_eq] using hinv
  · split
    · refine ⟨hinv, ?_⟩
      intro sr' heq
      cases heq
      exact hnew
    · exact ⟨hinv, fun _ h => by cases h⟩

private theorem canonVerdict_store {ctx : Ctx n} {level : Nat} {st : Search n}
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows) :
    VerdictInv ctx (canonVerdict ctx level st) := by
  have hzero := canongInv_zero (ctx := ctx) st.lab (canongInv_size hinv)
  by_cases hcomp : st.compCanon = 0
  · by_cases hlevel : level < st.canonlevel
    · simpa only [canonVerdict, hcomp, beq_self_eq_true, ite_true, hlevel, Id.run_pure, apply_ite Id.run]
        using verdict_store ctx 0 { st with compCanon := 1 } hinv hzero
    · have hr := (leafEvent_faithful (lab := st.lab) hinv).2
      simpa only [canonVerdict, hcomp, beq_self_eq_true, ite_true, hlevel, ite_false, Id.run_pure, apply_ite Id.run]
        using verdict_store ctx
          (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows) st.lab).2
          { st with
            canong := updatecan ctx st.canong st.canonlab st.samerows
            samerows := n
            compCanon := (testcanlab ctx (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 }
          hr.1 hr.2
  · simpa only [canonVerdict, beq_eq_false_iff_ne.mpr hcomp, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run]
      using verdict_store ctx 0 st hinv hzero

/-- Classification preserves the canonical store and prepares any better
candidate for installation, independently of the comparison-code invariant. -/
theorem classify_store {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows) :
    VerdictInv ctx (classify ctx level numcells st) := by
  rw [classify_eq]
  split
  · exact ⟨hinv, fun _ h => by cases h⟩
  · split
    · exact ⟨hinv, fun _ h => by cases h⟩
    · split
      · dsimp only
        split
        · exact ⟨by simpa only [scatter_eq] using hinv, fun _ h => by cases h⟩
        · exact canonVerdict_store (by simpa only [scatter_eq] using hinv)
      · exact canonVerdict_store hinv

/-- Code-one admission is precisely the first-reference scatter, accepted
by the cheap boundary or by an explicit automorphism scan. -/
theorem classify_first {ctx : Ctx n} {level numcells : Nat} {st out : Search n}
    (hauto : classify ctx level numcells st = (.autoFirst, out)) :
    numcells = n ∧ st.eqlevFirst = level ∧ out = scatter st.firstlab st ∧
      (st.noncheaplevel ≤ st.gcaFirst ∨ isautom ctx out.workperm = true) := by
  rw [classify_eq] at hauto
  split at hauto
  · cases hauto
  · split at hauto
    · cases hauto
    · rename_i hnc
      split at hauto
      · rename_i heq
        dsimp only at hauto
        split at hauto
        · rename_i hguard
          have hout : out = scatter st.firstlab st := (Prod.mk.inj hauto).2.symm
          refine ⟨by simpa using hnc, by simpa using heq, hout, ?_⟩
          rw [hout]
          simpa only [scatter_eq, Bool.or_eq_true, decide_eq_true_eq] using hguard
        · exact (canonVerdict_ne ctx level _ (congrArg Prod.fst hauto)).elim
      · exact (canonVerdict_ne ctx level _ (congrArg Prod.fst hauto)).elim

/-- The restored code-one admission is checked whenever the two histories
at its cheap ancestor are available. -/
theorem classify_first_checked {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st out : Search n}
    (hauto : classify ctx level numcells st = (.autoFirst, out))
    (hwork : st.workperm.size = n)
    (hfirst : st.firstlab.size = n) (hfirstPerm : st.firstlab.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n))
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hhistory : st.noncheaplevel ≤ st.gcaFirst →
      ∃ root current, ∃ href : FirstRef ctx tcLevel st.gcaFirst root st,
        Depth href.last st ∧ SubtreeOk ctx st.gcaFirst root ∧
        FollowsPerm ctx st.firsttc st.gcaFirst root level current ∧
        (∀ i, i < n → current.ptn[i]! ≤ level) ∧ st.lab = current.lab) :
    checkAutom ctx.g out.workperm = true := by
  obtain ⟨_, heq, hout, hguard⟩ := classify_first hauto
  rcases hguard with hcheap | hscan
  · obtain ⟨root, current, href, hdepth, hsmall, hcurrent, hdisc, hl⟩ := hhistory hcheap
    rw [hout]
    exact href.scatter (by rw [← heq]; exact hdepth.1) hgsz hsymm hloop hsmall hcurrent hdisc hl hwork
  · rw [hout] at hscan ⊢
    exact scatter_isautom hwork hfirst hfirstPerm hlab hlabPerm hsymm hloop hscan

/-- Code-two admission is checked by equality with the installed canonical rows. -/
theorem classify_canon_checked {ctx : Ctx n} {level numcells : Nat} {st out : Search n}
    (hauto : classify ctx level numcells st = (.autoCanon, out))
    (hinv : CanongInv ctx st.canong st.canonlab st.samerows)
    (hwork : st.workperm.size = n)
    (href : st.canonlab.size = n) (hrefPerm : st.canonlab.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n)) :
    checkAutom ctx.g out.workperm = true := by
  rw [classify_eq] at hauto
  split at hauto
  · cases hauto
  · split at hauto
    · cases hauto
    · split at hauto
      · dsimp only at hauto
        split at hauto
        · cases hauto
        · apply canonVerdict_checked hauto
          · simpa only [scatter_eq] using hinv
          · exact (scatter_size st.firstlab st).trans hwork
          · simpa only [scatter_eq] using href
          · simpa only [scatter_eq] using hrefPerm
          · simpa only [scatter_eq] using hlab
          · simpa only [scatter_eq] using hlabPerm
      · exact canonVerdict_checked hauto hinv hwork href hrefPerm hlab hlabPerm

private theorem admit_store {ctx : Ctx n} {st : Search n}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    CanongInv ctx (admit st).canong (admit st).canonlab (admit st).samerows := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> exact h

private theorem pruneReturn_store {ctx : Ctx n} {level : Nat} {st : Search n}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    let out := (pruneReturn level st).2
    CanongInv ctx out.canong out.canonlab out.samerows := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals exact h

/-- Acting on a justified verdict preserves the canonical row-store invariant. -/
theorem leafExit_store {ctx : Ctx n} {leaf : Leaf} {level : Nat} {st : Search n}
    (h : VerdictInv ctx (leaf, st)) :
    let out := (leafExit leaf level st).2
    CanongInv ctx out.canong out.canonlab out.samerows := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | exact h.1
    | exact admit_store h.1
    | exact pruneReturn_store h.1
    | exact pruneReturn_store (h.2 _ rfl)

end Hex.GraphIso.Nauty.Engine
