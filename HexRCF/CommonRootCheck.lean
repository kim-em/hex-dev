/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SturmCheck

public section

/-!
# Multiplication-checkable common roots

A common-root package is checked once for each distinct nonconstant atom
polynomial. Its exact identities witness divisibility by a supplied common-root
polynomial and a scaled Bezout relation. A nonconstant common-root polynomial
also carries one generalized Sturm replay, shared by every carrier root cell.
Real-root and cell semantics live in `HexRCF.CommonRoot`.
-/

namespace Hex.RCF

/-- Multiplication-checkable witnesses for the common roots of an atom and a
carrier polynomial. The atom and carrier themselves are external checker
inputs, so certificate data cannot silently substitute different polynomials.
-/
structure CommonRootCert where
  /-- Proposed common-root polynomial. -/
  gcd : ZPoly
  /-- Quotient witnessing that the common-root polynomial divides the atom. -/
  atomFactor : ZPoly
  /-- Quotient witnessing that the common-root polynomial divides the carrier. -/
  carrierFactor : ZPoly
  /-- Atom coefficient in the scaled Bezout identity. -/
  atomCoeff : ZPoly
  /-- Carrier coefficient in the scaled Bezout identity. -/
  carrierCoeff : ZPoly
  /-- Nonzero integer scale in the Bezout identity. -/
  scale : Int
  /-- Cached replay for a nonconstant common-root polynomial. A nonzero
  constant common-root polynomial uses `none`. -/
  replay : Option SturmReplay

namespace CommonRootCert

/-- Validate the constant/nonconstant replay branch. -/
@[expose]
def checkReplay (cert : CommonRootCert) : Bool :=
  match cert.replay with
  | none => decide (cert.gcd.size = 1)
  | some replay =>
      -- The replay checker already implies this degree bound. Keeping the
      -- guard makes the constant/nonconstant trust boundary explicit.
      decide (0 < cert.gcd.degree?.getD 0) && replay.check cert.gcd

/-- Proposition-level replay facts recovered from `checkReplay`. -/
@[expose]
def ReplayValid (cert : CommonRootCert) : Prop :=
  match cert.replay with
  | none => cert.gcd.size = 1
  | some replay =>
      0 < cert.gcd.degree?.getD 0 ∧ replay.check cert.gcd = true

/-- Check the divisibility and scaled Bezout identities against the external
atom and carrier polynomials. -/
@[expose]
def check (atom carrier : ZPoly) (cert : CommonRootCert) : Bool :=
  decide (cert.scale ≠ 0) &&
  DensePoly.beqCoeffs atom (cert.gcd * cert.atomFactor) &&
  DensePoly.beqCoeffs carrier (cert.gcd * cert.carrierFactor) &&
  DensePoly.beqCoeffs
    (cert.atomCoeff * atom + cert.carrierCoeff * carrier)
    (DensePoly.scale cert.scale cert.gcd) &&
  cert.checkReplay

/-- Proposition-level facts recovered from the common-root checker. -/
@[expose]
def Valid (atom carrier : ZPoly) (cert : CommonRootCert) : Prop :=
  cert.scale ≠ 0 ∧
  atom = cert.gcd * cert.atomFactor ∧
  carrier = cert.gcd * cert.carrierFactor ∧
  cert.atomCoeff * atom + cert.carrierCoeff * carrier =
    DensePoly.scale cert.scale cert.gcd ∧
  cert.ReplayValid

/-- Soundness of the constant/nonconstant replay branch. -/
theorem checkReplay_sound {cert : CommonRootCert}
    (h : cert.checkReplay = true) : cert.ReplayValid := by
  cases hreplay : cert.replay with
  | none => simpa [checkReplay, ReplayValid, hreplay] using h
  | some replay => simpa [checkReplay, ReplayValid, hreplay] using h

/-- Soundness of the executable common-root checker. -/
theorem check_sound {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : cert.check atom carrier = true) : cert.Valid atom carrier := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hscale, hatom⟩, hcarrier⟩, hbezout⟩, hreplay⟩ := h
  exact ⟨hscale, DensePoly.eq_of_beqCoeffs hatom,
    DensePoly.eq_of_beqCoeffs hcarrier,
    DensePoly.eq_of_beqCoeffs hbezout, checkReplay_sound hreplay⟩

/-- A checked common-root polynomial is nonzero in both certificate branches. -/
theorem gcd_ne_zero {atom carrier : ZPoly} {cert : CommonRootCert}
    (h : cert.check atom carrier = true) : cert.gcd ≠ 0 := by
  have hvalid := (check_sound h).2.2.2.2
  cases hreplay : cert.replay with
  | none =>
      simp only [ReplayValid, hreplay] at hvalid
      intro hzero
      rw [hzero] at hvalid
      simp at hvalid
  | some replay =>
      simp only [ReplayValid, hreplay] at hvalid
      exact SturmReplay.head_ne_zero hvalid.2

/-- Recover the checked replay in the nonconstant certificate branch. -/
theorem replay_of_check {atom carrier : ZPoly} {cert : CommonRootCert}
    {replay : SturmReplay} (h : cert.check atom carrier = true)
    (hreplay : cert.replay = some replay) : replay.check cert.gcd = true := by
  have hvalid := (check_sound h).2.2.2.2
  simp only [ReplayValid, hreplay] at hvalid
  exact hvalid.2

/-- Decide whether the cached common-root polynomial has a root in an
interval. The constant branch is root-free; the nonconstant branch reads its
shared generalized Sturm replay. -/
@[expose]
def hasRoot (cert : CommonRootCert) (I : DyadicInterval) : Bool :=
  match cert.replay with
  | none => false
  | some replay => decide (replay.count I = 1)

end CommonRootCert

end Hex.RCF
