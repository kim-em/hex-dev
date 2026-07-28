/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.IsolationCheck
public import HexRealRoots.Prec
import Init.Data.Order.Lemmas

public section

/-!
# Strict separation and endpoint checks for RCF cells

The untrusted builders in this module bisect touching generalized isolations
with counts from a cached `SturmReplay`. Their output is retained only when a
small checker revalidates all isolation facts and emitted strict gaps. Endpoint
classification likewise uses exact dyadic comparison, literal replay counts,
and exact polynomial evaluation. Real-root semantics live in
`HexRCF.Separation`.
-/

namespace Hex.RCF

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

/-- Strict validation exposes its strict-gap component. -/
theorem gaps_of_checkStrict {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.checkStrict replay = true) : cert.checkGaps = true := by
  simp only [checkStrict, Bool.and_eq_true] at h
  exact h.2

/-- Every adjacent pair accepted by the strict-gap walk is strictly separated. -/
theorem gap_of_check {cert : IsolationCert} (h : cert.checkGaps = true)
    (i : Nat) (hi : i + 1 < cert.intervals.size) :
    (cert.intervals[i]'(by omega)).upper <
      (cert.intervals[i + 1]'hi).lower := by
  have hmem : i ∈ List.range (cert.intervals.size - 1) := List.mem_range.mpr (by omega)
  have hstep := (List.all_eq_true.mp h) i hmem
  simp only [hi, dif_pos] at hstep
  exact of_decide_eq_true hstep

/-- Transitivity of strict order on dyadic numbers. -/
private theorem dlt_trans {a b c : Dyadic} (hab : a < b) (hbc : b < c) : a < c := by
  rw [← Dyadic.toRat_lt_toRat_iff] at hab hbc ⊢
  exact Std.lt_trans hab hbc

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

/-- Classify one isolated root against an exact dyadic endpoint. In the
interior case, the literal replay count on the prefix interval determines the
side, with exact polynomial evaluation resolving equality. -/
@[expose]
def classify? (f : ZPoly) (replay : SturmReplay)
    (I : DyadicInterval) (endpoint : Dyadic) : Option RootCmp :=
  if hleft : endpoint ≤ I.lower then some .gt
  else if _hright : I.upper < endpoint then some .lt
  else
    -- `Dyadic.not_lt` uses the converse naming convention from Mathlib and
    -- turns `¬e ≤ l` into `l < e`.
    let initial := DyadicInterval.mk I.lower endpoint (Dyadic.not_lt.mp hleft)
    if replay.count initial = 0 then some .gt
    else if replay.count initial = 1 then
      if Hex.dyadicSign (f.evalDyadic endpoint) = 0 then some .eq else some .lt
    else none

/-- Recompute and check a claimed endpoint comparison. Sound use additionally
requires the outer certificate to establish `replay.check f`. -/
@[expose]
def checkCmp (f : ZPoly) (replay : SturmReplay) (I : DyadicInterval)
    (endpoint : Dyadic) (claim : RootCmp) : Bool :=
  decide (classify? f replay I endpoint = some claim)

/-- Bisect one raw interval and retain a count-one half. The midpoint variation
is shared between the two candidate counts. -/
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
structural fuel is exhausted. Genuine overlaps and malformed count data are
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

/-- Left-to-right separation scan. Refining a later interval only shrinks it,
so honest input preserves every strict gap already emitted. -/
def separateList? (p : ZPoly) (replay : SturmReplay) :
    List DyadicInterval → Option (List DyadicInterval)
  | [] => some []
  | first :: rest => separateFrom? p replay first rest

/-- Run untrusted strict separation and retain only checker-approved output.
The caller pairs `p` with a replay checked against it. A mismatch can only
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
theorem check_separate {p : ZPoly} {replay : SturmReplay}
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
