/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Replay

public section

/-!
# The Mathlib-free ECPP checker

A successful step checks the curve equation and discriminant unit, the exact
integer size bound, and the complete scalar transcript for the child subject.
-/

namespace Hex.ECPP

/-- Check one step after obtaining its child subject. -/
@[expose]
def checkStep (n a b x y discrInv : Nat) (inverses : List Nat) (q : Nat) : Bool :=
  3 < n && (n % 6 == 1 || n % 6 == 5) &&
    2 ≤ q && q < n &&
    a < n && b < n && x < n && y < n && discrInv < n &&
    onCurve n a b x y &&
    (4 * a * a * a + 27 * b * b) * discrInv % n == 1 &&
    sizeBound n q &&
    replayDone n a b q (.affine x y) inverses

/-- A checked terminal Hex certificate or a checked ECPP step. -/
@[expose]
def check : Cert → Bool
  | .base cert => Hex.Nat.checkPrime cert
  | .step n a b x y discrInv inverses child =>
      check child && checkStep n a b x y discrInv inverses child.subject

/-- Bind acceptance to a caller supplied subject. -/
@[expose]
def checkAt (n : Nat) (cert : Cert) : Bool :=
  cert.subject == n && check cert

theorem checkStep_canonical {n a b x y discrInv q : Nat}
    {inverses : List Nat}
    (h : checkStep n a b x y discrInv inverses q = true) :
    a < n ∧ b < n ∧ x < n ∧ y < n ∧ discrInv < n := by
  simp only [checkStep, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_iff, beq_iff_eq] at h
  grind

theorem checkStep_facts {n a b x y discrInv q : Nat} {inverses : List Nat}
    (h : checkStep n a b x y discrInv inverses q = true) :
    3 < n ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧ 2 ≤ q ∧ q < n ∧
      onCurve n a b x y = true ∧
      (4 * a * a * a + 27 * b * b) * discrInv % n = 1 ∧
      sizeBound n q = true ∧
      replay n a b q (.affine x y) inverses = some (.infinity, []) := by
  simp only [checkStep, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_iff, beq_iff_eq] at h
  have hreplay := replayDone_eq_true_iff.mp h.2
  grind

theorem checkAt_subject {n : Nat} {cert : Cert}
    (h : checkAt n cert = true) : cert.subject = n := by
  simp only [checkAt, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem checkAt_check {n : Nat} {cert : Cert}
    (h : checkAt n cert = true) : check cert = true := by
  simp only [checkAt, Bool.and_eq_true] at h
  exact h.2

end Hex.ECPP
