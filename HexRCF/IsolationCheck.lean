/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SturmCheck

public section

/-!
# Generalized literal isolation checks

An isolation certificate stores only raw dyadic intervals. Its Boolean checker
reads root counts from an independently validated `SturmReplay`, checks one
root per interval, adjacent ordering, and completeness. Mathlib-facing literal
isolation and real-root semantics live in `HexRCF.Isolations`.
-/

namespace Hex.RCF

/-- Raw intervals proposed as an ordered, complete isolation of the roots of
the head polynomial of a generalized Sturm replay. -/
structure IsolationCert where
  /-- Proposed half-open root intervals in ascending order. -/
  intervals : Array DyadicInterval

namespace IsolationCert

/-- Check that every supplied interval has literal replay count one. -/
@[expose]
def checkCounts (replay : SturmReplay) (cert : IsolationCert) : Bool :=
  (List.range cert.intervals.size).all fun i =>
    if h : i < cert.intervals.size then
      decide (replay.count (cert.intervals[i]'h) = 1)
    else false

/-- Check the emitted order in linear time using only adjacent pairs. This is
intentionally non-strict for half-open isolations. Strict gaps are checked by
the later cell-separation certificate. -/
@[expose]
def checkOrder (cert : IsolationCert) : Bool :=
  (List.range (cert.intervals.size - 1)).all fun i =>
    if h : i + 1 < cert.intervals.size then
      decide ((cert.intervals[i]'(by omega)).upper ≤
        (cert.intervals[i + 1]'h).lower)
    else false

/-- Validate literal interval counts, ordering, and total completeness. Replay
validation is a separate premise so an outer checker need not reduce it twice. -/
@[expose]
def check (replay : SturmReplay) (cert : IsolationCert) : Bool :=
  cert.checkCounts replay && cert.checkOrder &&
    decide (replay.total = (cert.intervals.size : Int))

/-- Every interval accepted by the count walk has literal count one. -/
theorem count_one_of_check {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.checkCounts replay = true) (i : Fin cert.intervals.size) :
    replay.count cert.intervals[i] = 1 := by
  have hmem : i.val ∈ List.range cert.intervals.size := List.mem_range.mpr i.isLt
  have hcount := (List.all_eq_true.mp h) i.val hmem
  simp only [i.isLt, dif_pos] at hcount
  exact of_decide_eq_true hcount

/-- Each adjacent interval pair accepted by the order walk is separated in the
non-strict half-open sense. -/
theorem adjacent_of_check {cert : IsolationCert} (h : cert.checkOrder = true)
    (i : Nat) (hi : i + 1 < cert.intervals.size) :
    (cert.intervals[i]'(by omega)).upper ≤
      (cert.intervals[i + 1]'hi).lower := by
  have hmem : i ∈ List.range (cert.intervals.size - 1) := List.mem_range.mpr (by omega)
  have hstep := (List.all_eq_true.mp h) i hmem
  simp only [hi, dif_pos] at hstep
  exact of_decide_eq_true hstep

/-- Derive non-strict dyadic order from strict dyadic order. -/
private theorem dyadic_le_of_lt {a b : Dyadic} (h : a < b) : a ≤ b := by
  rcases Dyadic.le_total a b with hle | hle
  · exact hle
  · exact absurd h (Dyadic.not_le.mpr hle)

/-- Adjacent ordering implies the all-pairs ordering used by the semantic
literal-isolation layer. -/
theorem ordered_of_check {cert : IsolationCert} (h : cert.checkOrder = true) :
    ∀ i j : Fin cert.intervals.size, i < j →
      cert.intervals[i].upper ≤ cert.intervals[j].lower := by
  have aux : ∀ (j : Nat) (hj : j < cert.intervals.size) (i : Nat) (_hij : i < j),
      (cert.intervals[i]'(by omega)).upper ≤ (cert.intervals[j]'hj).lower := by
    intro j
    induction j with
    | zero => intro _ i hij; omega
    | succ j ih =>
        intro hj i hij
        rcases Nat.lt_or_ge i j with hlt | hge
        · have hjlt : j < cert.intervals.size := by omega
          have step1 := ih hjlt i hlt
          have step2 : (cert.intervals[j]'hjlt).lower ≤
              (cert.intervals[j]'hjlt).upper :=
            dyadic_le_of_lt (cert.intervals[j]'hjlt).lt
          have step3 := adjacent_of_check h j (by omega)
          exact Dyadic.le_trans step1 (Dyadic.le_trans step2 step3)
        · have hij' : i = j := by omega
          subst hij'
          exact adjacent_of_check h i (by omega)
  intro i j hij
  exact aux j.val j.isLt i.val hij

/-- The completeness equality recovered from the Boolean isolation checker. -/
theorem complete_of_check {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.check replay = true) :
    replay.total = (cert.intervals.size : Int) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The count component recovered from the combined checker. -/
theorem counts_of_check {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.check replay = true) : cert.checkCounts replay = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.1

/-- The order component recovered from the combined checker. -/
theorem order_of_check {replay : SturmReplay} {cert : IsolationCert}
    (h : cert.check replay = true) : cert.checkOrder = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.2

end IsolationCert

end Hex.RCF
