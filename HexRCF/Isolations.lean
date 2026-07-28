/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.IsolationCheck
public import HexRCF.SturmReplay
public import HexRealRootsMathlib.LiteralIsolations

public section

/-!
# Semantics of generalized literal isolations

The Mathlib-free certificate and checker live in `HexRCF.IsolationCheck`.
Soundness packages accepted raw intervals into `LiteralIsolations` and applies
the generic semantic isolation theorem. It never identifies the replay with
the executable pseudo-remainder chain.
-/

namespace Hex.RCF

open HexRealRootsMathlib

namespace IsolationCert

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

/-- Converting an isolation certificate preserves the number of intervals. -/
@[simp] theorem size_toLiteral (replay : SturmReplay) (cert : IsolationCert)
    (h : cert.check replay = true) :
    (cert.toLiteral replay h).isolations.size = cert.intervals.size := by
  simp [toLiteral]

/-- The interval at each index is unchanged by conversion to literal isolations. -/
theorem interval_toLiteral (replay : SturmReplay) (cert : IsolationCert)
    (h : cert.check replay = true)
    (i : Nat) (hi : i < (cert.toLiteral replay h).isolations.size) :
    ((cert.toLiteral replay h).isolations[i]'hi).interval =
      cert.intervals[i]'(by simpa using hi) := by
  simp [toLiteral]

/-- Every accepted interval contains exactly one real root of the replay head. -/
theorem existsUnique_root {f : ZPoly} {replay : SturmReplay}
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
