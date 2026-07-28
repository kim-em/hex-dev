/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SeparationCheck
public import HexRCF.Isolations

public section

/-!
# Semantics of strict separation and endpoint order

The Mathlib-free strict-gap checker, endpoint classifier, and refinement
builders live in `HexRCF.SeparationCheck`. The theorems in this file connect
their accepted dyadic data to the corresponding real-root order.
-/

namespace Hex.RCF

open HexRealRootsMathlib

namespace IsolationCert

/-- Strictly separated intervals contain roots in the corresponding strict
order. -/
theorem roots_lt_of_check {cert : IsolationCert} (h : cert.checkGaps = true)
    {i j : Fin cert.intervals.size} (hij : i < j) {ri rj : ℝ}
    (hi : Literal.InInterval cert.intervals[i] ri)
    (hj : Literal.InInterval cert.intervals[j] rj) : ri < rj := by
  have hgap := toReal_lt_toReal (gaps_of_check h i j hij)
  simp only [Literal.InInterval] at hi hj
  exact lt_of_le_of_lt hi.2 (lt_trans hgap hj.1)

end IsolationCert

namespace Separation

namespace RootCmp

/-- Semantic interpretation of an endpoint comparison. -/
@[expose]
def Holds : RootCmp → ℝ → ℝ → Prop
  | .lt, root, endpoint => root < endpoint
  | .eq, root, endpoint => root = endpoint
  | .gt, root, endpoint => endpoint < root

end RootCmp

/-- Every successful endpoint classification has the stated order against the
unique root in the accepted isolation. -/
theorem classify_sound {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size)
    (endpoint : Dyadic) {cmp : RootCmp}
    (hcmp : classify? f replay cert.intervals[i] endpoint = some cmp) :
    ∃! root : ℝ, (toPolyℝ f).IsRoot root ∧
      Literal.InInterval cert.intervals[i] root ∧
      cmp.Holds root (Dyadic.toReal endpoint) := by
  classical
  obtain ⟨root, hroot, huniq⟩ :=
    IsolationCert.exists_unique_root_of_check hreplay hcert i
  have hP : toPolyℝ f ≠ 0 := by
    intro hzero
    exact SturmReplay.head_ne_zero hreplay (toPolyℝ_eq_zero_iff.mp hzero)
  refine ⟨root, ⟨hroot.1, hroot.2, ?_⟩, ?_⟩
  · unfold classify? at hcmp
    split at hcmp
    next hleft =>
      have heq : RootCmp.gt = cmp := Option.some.inj hcmp
      subst cmp
      exact lt_of_le_of_lt (toReal_le_toReal hleft) hroot.2.1
    next hleft =>
      split at hcmp
      next hright =>
        have heq : RootCmp.lt = cmp := Option.some.inj hcmp
        subst cmp
        exact lt_of_le_of_lt hroot.2.2 (toReal_lt_toReal hright)
      next hright =>
        let initial := DyadicInterval.mk cert.intervals[i].lower endpoint
          (Dyadic.not_lt.mp hleft)
        have hend : endpoint ≤ cert.intervals[i].upper := Dyadic.not_le.mp hright
        change (if replay.count initial = 0 then some RootCmp.gt
          else if replay.count initial = 1 then
            if Hex.dyadicSign (f.evalDyadic endpoint) = 0 then some RootCmp.eq
            else some RootCmp.lt
          else none) = some cmp at hcmp
        split at hcmp
        next hzero =>
          have heq : RootCmp.gt = cmp := Option.some.inj hcmp
          subst cmp
          apply lt_of_not_ge
          intro hle
          have hmem : root ∈ Literal.rootsIn (toPolyℝ f) initial := by
            simp only [Literal.rootsIn, Multiset.mem_filter]
            exact ⟨Polynomial.mem_roots'.mpr ⟨hP, hroot.1⟩,
              hroot.2.1, hle⟩
          have hcard : (Literal.rootsIn (toPolyℝ f) initial).card = 0 := by
            have hc := SturmReplay.count_eq_card_roots hreplay initial
            rw [hzero] at hc
            exact_mod_cast hc.symm
          have hpos : 0 < (Literal.rootsIn (toPolyℝ f) initial).card := by
            apply Multiset.card_pos.mpr
            intro hempty
            rw [hempty] at hmem
            simp at hmem
          omega
        next hzero =>
          split at hcmp
          next hone =>
            have hcard : (Literal.rootsIn (toPolyℝ f) initial).card = 1 := by
              have hc := SturmReplay.count_eq_card_roots hreplay initial
              rw [hone] at hc
              exact_mod_cast hc.symm
            obtain ⟨y, hy⟩ := Multiset.card_eq_one.mp hcard
            have hymem : y ∈ Literal.rootsIn (toPolyℝ f) initial := by
              rw [hy]
              simp
            simp only [Literal.rootsIn, Multiset.mem_filter] at hymem
            have hyI : Literal.InInterval cert.intervals[i] y := by
              exact ⟨hymem.2.1,
                le_trans hymem.2.2 (toReal_le_toReal hend)⟩
            have hyr : y = root :=
              huniq y ⟨(Polynomial.mem_roots'.mp hymem.1).2, hyI⟩
            have hrootEnd : root ≤ Dyadic.toReal endpoint := by
              rw [← hyr]
              exact hymem.2.2
            split at hcmp
            next heval =>
              have heq : RootCmp.eq = cmp := Option.some.inj hcmp
              subst cmp
              have hendRoot : (toPolyℝ f).IsRoot (Dyadic.toReal endpoint) :=
                (evalSign_zero_iff f endpoint).mp heval
              have hendI : Literal.InInterval cert.intervals[i]
                  (Dyadic.toReal endpoint) := by
                exact ⟨toReal_lt_toReal (Dyadic.not_lt.mp hleft),
                  toReal_le_toReal hend⟩
              exact (huniq _ ⟨hendRoot, hendI⟩).symm
            next heval =>
              have heq : RootCmp.lt = cmp := Option.some.inj hcmp
              subst cmp
              apply lt_of_le_of_ne hrootEnd
              intro heqRoot
              apply heval
              apply (evalSign_zero_iff f endpoint).mpr
              rw [← heqRoot]
              exact hroot.1
          next hone => simp at hcmp
  · intro other hother
    exact huniq other ⟨hother.1, hother.2.1⟩

/-- Valid replay isolations classify every dyadic endpoint: the interior
prefix count cannot exceed the count-one enclosing interval. -/
theorem classify_exists {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size)
    (endpoint : Dyadic) :
    ∃ cmp, classify? f replay cert.intervals[i] endpoint = some cmp := by
  classical
  unfold classify?
  split
  · exact ⟨RootCmp.gt, rfl⟩
  split
  · exact ⟨RootCmp.lt, rfl⟩
  next hleft hright =>
    let initial := DyadicInterval.mk cert.intervals[i].lower endpoint
      (Dyadic.not_lt.mp hleft)
    have hend : endpoint ≤ cert.intervals[i].upper := Dyadic.not_le.mp hright
    have hsub : Literal.rootsIn (toPolyℝ f) initial ≤
        Literal.rootsIn (toPolyℝ f) cert.intervals[i] := by
      simp only [Literal.rootsIn]
      apply Multiset.le_filter.mpr
      refine ⟨Multiset.filter_le _ _, ?_⟩
      intro root hroot
      simp only [Multiset.mem_filter] at hroot ⊢
      exact ⟨hroot.2.1, le_trans hroot.2.2 (toReal_le_toReal hend)⟩
    have hfull : (Literal.rootsIn (toPolyℝ f) cert.intervals[i]).card = 1 := by
      have hcount := IsolationCert.count_one_of_check
        (IsolationCert.counts_of_check hcert) i
      have hc := SturmReplay.count_eq_card_roots hreplay cert.intervals[i]
      rw [hcount] at hc
      exact_mod_cast hc.symm
    have hle : (Literal.rootsIn (toPolyℝ f) initial).card ≤ 1 := by
      rw [← hfull]
      exact Multiset.card_le_card hsub
    have hcount := SturmReplay.count_eq_card_roots hreplay initial
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
    · have hzero' : replay.count initial = 0 := by
        rw [hcount]
        exact_mod_cast hzero
      change ∃ cmp, (if replay.count initial = 0 then some RootCmp.gt
        else if replay.count initial = 1 then
          if Hex.dyadicSign (f.evalDyadic endpoint) = 0 then some RootCmp.eq
          else some RootCmp.lt
        else none) = some cmp
      exact ⟨RootCmp.gt, by simp [hzero']⟩
    · have hone' : replay.count initial = 1 := by
        rw [hcount]
        exact_mod_cast hone
      change ∃ cmp, (if replay.count initial = 0 then some RootCmp.gt
        else if replay.count initial = 1 then
          if Hex.dyadicSign (f.evalDyadic endpoint) = 0 then some RootCmp.eq
          else some RootCmp.lt
        else none) = some cmp
      by_cases heval : Hex.dyadicSign (f.evalDyadic endpoint) = 0
      · exact ⟨RootCmp.eq, by simp [hone', heval]⟩
      · exact ⟨RootCmp.lt, by simp [hone', heval]⟩

/-- A checked comparison claim inherits the classifier soundness theorem. -/
theorem checkCmp_sound {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size)
    (endpoint : Dyadic) (claim : RootCmp)
    (hclaim : checkCmp f replay cert.intervals[i] endpoint claim = true) :
    ∃! root : ℝ, (toPolyℝ f).IsRoot root ∧
      Literal.InInterval cert.intervals[i] root ∧
      claim.Holds root (Dyadic.toReal endpoint) := by
  apply classify_sound hreplay hcert i endpoint
  exact of_decide_eq_true hclaim

end Separation

end Hex.RCF
