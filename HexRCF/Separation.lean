/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.Isolations
public import HexRealRoots.Prec

public section

/-!
# Strict separation and endpoint order for RCF cells

The untrusted builder in this module bisects touching generalized isolations
with counts from a cached `SturmReplay`.  Its output is retained only when a
small checker revalidates all isolation facts and the emitted strict gaps.  The
kernel checker never evaluates separation bounds or runs refinement.
-/

namespace Hex.RCF

open HexRealRootsMathlib

namespace IsolationCert

/-- Check strict gaps between every adjacent pair of emitted intervals. -/
@[expose]
def checkGaps (cert : IsolationCert) : Bool :=
  (List.range (cert.intervals.size - 1)).all fun i =>
    if h : i + 1 < cert.intervals.size then
      decide ((cert.intervals[i]'(by omega)).upper <
        (cert.intervals[i + 1]'h).lower)
    else false

/-- Validate generalized isolation and strict adjacent separation. -/
@[expose]
def checkStrict (replay : SturmReplay) (cert : IsolationCert) : Bool :=
  cert.check replay && cert.checkGaps

/-- Recover the underlying generalized isolation check. -/
theorem check_of_checkStrict {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.checkStrict replay = true) : cert.check replay = true := by
  simp only [checkStrict, Bool.and_eq_true] at h
  exact h.1

/-- Every adjacent pair accepted by the strict-gap walk is strictly separated. -/
theorem gap_of_check {cert : IsolationCert} (h : cert.checkGaps = true)
    (i : Nat) (hi : i + 1 < cert.intervals.size) :
    (cert.intervals[i]'(by omega)).upper <
      (cert.intervals[i + 1]'hi).lower := by
  have hmem : i ∈ List.range (cert.intervals.size - 1) := List.mem_range.mpr (by omega)
  have hstep := (List.all_eq_true.mp h) i hmem
  simp only [hi, dif_pos] at hstep
  exact of_decide_eq_true hstep

/-- Transitivity for the core dyadic strict order. -/
private theorem dlt_trans {a b c : Dyadic} (hab : a < b) (hbc : b < c) : a < c := by
  rw [← Dyadic.toRat_lt_toRat_iff] at hab hbc ⊢
  exact lt_trans hab hbc

/-- Strict adjacent gaps imply strict separation for every earlier/later pair. -/
theorem gaps_of_check {cert : IsolationCert} (h : cert.checkGaps = true) :
    ∀ i j : Fin cert.intervals.size, i < j →
      cert.intervals[i].upper < cert.intervals[j].lower := by
  have aux : ∀ (j : Nat) (hj : j < cert.intervals.size) (i : Nat) (_hij : i < j),
      (cert.intervals[i]'(by omega)).upper < (cert.intervals[j]'hj).lower := by
    intro j
    induction j with
    | zero => intro _ i hij; omega
    | succ j ih =>
        intro hj i hij
        rcases Nat.lt_or_ge i j with hlt | hge
        · have hjlt : j < cert.intervals.size := by omega
          have step1 := ih hjlt i hlt
          have step2 := (cert.intervals[j]'hjlt).lt
          have step3 := gap_of_check h j (by omega)
          exact dlt_trans (dlt_trans step1 step2) step3
        · have hij' : i = j := by omega
          subst hij'
          exact gap_of_check h i (by omega)
  intro i j hij
  exact aux j.val j.isLt i.val hij

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

/-- The order of an isolated real root relative to an exact dyadic endpoint. -/
inductive RootCmp where
  /-- The isolated root is strictly below the endpoint. -/
  | lt
  /-- The isolated root equals the endpoint. -/
  | eq
  /-- The endpoint is strictly below the isolated root. -/
  | gt
  deriving DecidableEq, Repr

namespace RootCmp

/-- Semantic interpretation of an endpoint comparison. -/
@[expose]
def Holds : RootCmp → ℝ → ℝ → Prop
  | .lt, root, endpoint => root < endpoint
  | .eq, root, endpoint => root = endpoint
  | .gt, root, endpoint => endpoint < root

end RootCmp

/-- Classify one isolated root against an exact dyadic endpoint.  In the
interior case, the literal replay count on the prefix interval determines the
side, with exact polynomial evaluation resolving equality. -/
@[expose]
def classify? (f : ZPoly) (replay : SturmReplay)
    (I : DyadicInterval) (endpoint : Dyadic) : Option RootCmp :=
  if hleft : endpoint ≤ I.lower then some .gt
  else if _hright : I.upper < endpoint then some .lt
  else
    -- Core's names are the converses of the usual Mathlib convention:
    -- `Dyadic.not_lt` turns `¬e ≤ l` into `l < e`.
    let initial := DyadicInterval.mk I.lower endpoint (Dyadic.not_lt.mp hleft)
    if replay.count initial = 0 then some .gt
    else if replay.count initial = 1 then
      if Hex.dyadicSign (f.evalDyadic endpoint) = 0 then some .eq else some .lt
    else none

/-- Recompute and check a claimed endpoint comparison.  Sound use additionally
requires the outer certificate to establish `replay.check f`. -/
@[expose]
def checkCmp (f : ZPoly) (replay : SturmReplay) (I : DyadicInterval)
    (endpoint : Dyadic) (claim : RootCmp) : Bool :=
  decide (classify? f replay I endpoint = some claim)

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

/-- Bisect one raw interval and retain a count-one half.  The midpoint
variation is shared between the two candidate counts. -/
def refine1? (replay : SturmReplay) (I : DyadicInterval) : Option DyadicInterval :=
  let m := I.midpoint
  if hl : I.lower < m then
    let left := DyadicInterval.mk I.lower m hl
    let vlo := sturmVarAt replay.chain I.lower
    let vm := sturmVarAt replay.chain m
    if vlo - vm = 1 then some left
    else if hr : m < I.upper then
      let right := DyadicInterval.mk m I.upper hr
      let vhi := sturmVarAt replay.chain I.upper
      if vm - vhi = 1 then some right else none
    else none
  else none

/-- Separate a pair with an explicit structural fuel budget. -/
def refinePairWith? (replay : SturmReplay) :
    Nat → DyadicInterval → DyadicInterval →
      Option (DyadicInterval × DyadicInterval)
  | fuel, left, right =>
      if left.upper < right.lower then some (left, right)
      else if left.upper ≤ right.lower then
        match fuel with
        | 0 => none
        | fuel + 1 => do
            let left' ← refine1? replay left
            let right' ← refine1? replay right
            refinePairWith? replay fuel left' right'
      else none

/-- Refine both members of a touching pair until they have a strict gap or the
structural fuel is exhausted.  Genuine overlaps and malformed count data are
rejected. -/
def refinePair? (p : ZPoly) (replay : SturmReplay)
    (left right : DyadicInterval) : Option (DyadicInterval × DyadicInterval) :=
  let fuel := max
    ((Hex.ceilLog2Dyadic left.width + Hex.sepPrec p).toNat + 1)
    ((Hex.ceilLog2Dyadic right.width + Hex.sepPrec p).toNat + 1)
  refinePairWith? replay fuel left right

/-- Continue a left-to-right separation scan from its current interval. -/
def separateFrom? (p : ZPoly) (replay : SturmReplay)
    (previous : DyadicInterval) :
    List DyadicInterval → Option (List DyadicInterval)
  | [] => some [previous]
  | next :: rest =>
      if previous.upper < next.lower then do
        let tail ← separateFrom? p replay next rest
        pure (previous :: tail)
      else do
        let pair ← refinePair? p replay previous next
        let tail ← separateFrom? p replay pair.2 rest
        pure (pair.1 :: tail)

/-- Left-to-right separation scan.  Refining a later interval only shrinks it,
so honest input preserves every strict gap already emitted. -/
def separateList? (p : ZPoly) (replay : SturmReplay) :
    List DyadicInterval → Option (List DyadicInterval)
  | [] => some []
  | first :: rest => separateFrom? p replay first rest

/-- Run untrusted strict separation and retain only checker-approved output.
The caller pairs `p` with a replay checked against it; a mismatch can only
choose inadequate fuel and make this builder return `none`, because the output
checker reads counts solely from `replay`. -/
def separate? (p : ZPoly) (replay : SturmReplay)
    (cert : IsolationCert) : Option IsolationCert :=
  match separateList? p replay cert.intervals.toList with
  | none => none
  | some intervals =>
      let out : IsolationCert := ⟨intervals.toArray⟩
      if out.checkStrict replay then some out else none

/-- The public builder never returns an unchecked strict isolation array. -/
theorem check_of_separate_eq_some {p : ZPoly} {replay : SturmReplay}
    {input output : IsolationCert} (h : separate? p replay input = some output) :
    output.checkStrict replay = true := by
  unfold separate? at h
  split at h <;> rename_i hlist
  · simp at h
  · dsimp only at h
    split at h <;> rename_i hc
    · cases Option.some.inj h
      exact hc
    · simp at h

end Separation

end Hex.RCF
