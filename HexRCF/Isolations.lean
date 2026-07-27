/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SturmReplay
public import HexRealRootsMathlib.LiteralIsolations

public section

/-!
# Generalized literal isolations for RCF replay certificates

An isolation certificate stores only raw dyadic intervals.  Its Boolean
checker reads root counts from an independently validated `SturmReplay`, checks
one root per interval, adjacent ordering, and completeness.  Soundness packages
the raw intervals into `LiteralIsolations` and applies the generic semantic
isolation theorem; it never identifies the replay with the executable
pseudo-remainder chain.
-/

namespace Hex.RCF

open HexRealRootsMathlib

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

/-- Check the emitted order in linear time using only adjacent pairs.  This is
intentionally non-strict for half-open isolations; strict gaps are checked by
the later cell-separation certificate. -/
@[expose]
def checkOrder (cert : IsolationCert) : Bool :=
  (List.range (cert.intervals.size - 1)).all fun i =>
    if h : i + 1 < cert.intervals.size then
      decide ((cert.intervals[i]'(by omega)).upper ≤
        (cert.intervals[i + 1]'h).lower)
    else false

/-- Validate literal interval counts, ordering, and total completeness.  Replay
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

/-- `Dyadic` version of `le_of_lt`, derived from the core total order API. -/
private theorem dyadic_le_of_lt {a b : Dyadic} (h : a < b) : a ≤ b := by
  rcases Dyadic.le_total a b with hle | hle
  · exact hle
  · exact absurd h (Dyadic.not_le.mpr hle)

/-- Adjacent ordering implies the all-pairs ordering used by
`LiteralIsolations`. -/
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

/-- Package an accepted raw certificate into the generic literal-isolation
interface. -/
def toLiteral (replay : SturmReplay) (cert : IsolationCert)
    (h : cert.check replay = true) :
    LiteralIsolations replay.count replay.total where
  isolations := cert.intervals.mapFinIdx fun i _ hi =>
    { interval := cert.intervals[i]'hi
      count_one := count_one_of_check (counts_of_check h) ⟨i, hi⟩ }
  ordered := by
    intro i j hij
    let i' : Fin cert.intervals.size := ⟨i.val, by simpa using i.isLt⟩
    let j' : Fin cert.intervals.size := ⟨j.val, by simpa using j.isLt⟩
    have hij' : i' < j' := by simpa [i', j'] using hij
    have hord := ordered_of_check (order_of_check h) i' j' hij'
    simpa [i', j'] using hord
  complete := by
    simpa using complete_of_check h

@[simp] theorem size_toLiteral (replay : SturmReplay) (cert : IsolationCert)
    (h : cert.check replay = true) :
    (cert.toLiteral replay h).isolations.size = cert.intervals.size := by
  simp [toLiteral]

theorem interval_toLiteral (replay : SturmReplay) (cert : IsolationCert)
    (h : cert.check replay = true)
    (i : Nat) (hi : i < (cert.toLiteral replay h).isolations.size) :
    ((cert.toLiteral replay h).isolations[i]'hi).interval =
      cert.intervals[i]'(by simpa using hi) := by
  simp [toLiteral]

/-- Every accepted interval contains exactly one real root of the replay head. -/
theorem exists_unique_root_of_check {f : ZPoly} {replay : SturmReplay}
    {cert : IsolationCert} (hreplay : replay.check f = true)
    (hcert : cert.check replay = true) (i : Fin cert.intervals.size) :
    ∃! r : ℝ, (toPolyℝ f).IsRoot r ∧
      Literal.InInterval cert.intervals[i] r := by
  let iso : LiteralIsolation replay.count :=
    { interval := cert.intervals[i]
      count_one := count_one_of_check (counts_of_check hcert) i }
  exact iso.exists_unique_root (SturmReplay.head_ne_zero hreplay)
    (SturmReplay.count_eq_card_roots hreplay iso.interval)

/-- Accepted raw intervals isolate every real root of the replay head at a
unique original array index. -/
theorem isolates_of_check {f : ZPoly} {replay : SturmReplay} {cert : IsolationCert}
    (hreplay : replay.check f = true) (hcert : cert.check replay = true) :
    ∀ r : ℝ, (toPolyℝ f).IsRoot r →
      ∃! i : Fin cert.intervals.size,
        Literal.InInterval cert.intervals[i] r := by
  let out := cert.toLiteral replay hcert
  have hout := out.isolates (SturmReplay.head_ne_zero hreplay)
    (SturmReplay.squarefree_of_check hreplay)
    (fun i => SturmReplay.count_eq_card_roots hreplay out.isolations[i].interval)
    (SturmReplay.total_eq_card_roots hreplay)
  intro r hr
  obtain ⟨i, hi, huniq⟩ := hout r hr
  have hiBound : i.val < cert.intervals.size := by
    simpa only [out, size_toLiteral] using i.isLt
  let i' : Fin cert.intervals.size := ⟨i.val, hiBound⟩
  refine ⟨i', ?_, ?_⟩
  · rw [show out.isolations[i].interval = cert.intervals[i'] by
      simpa only [out, i', Fin.getElem_fin] using
        interval_toLiteral replay cert hcert i.val i.isLt] at hi
    exact hi
  · intro j hj
    have hjBound : j.val < out.isolations.size := by
      simpa only [out, size_toLiteral] using j.isLt
    let j' : Fin out.isolations.size := ⟨j.val, hjBound⟩
    have hj' : Literal.InInterval out.isolations[j'].interval r := by
      rw [show out.isolations[j'].interval = cert.intervals[j] by
        simpa only [out, j', Fin.getElem_fin] using
          interval_toLiteral replay cert hcert j'.val j'.isLt]
      exact hj
    have hji : j' = i := huniq j' hj'
    apply Fin.ext
    simpa only [j', i'] using congrArg Fin.val hji

end IsolationCert

end Hex.RCF
