/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPP.Replay

public section

/-!
# Checking elliptic curve primality certificates

The checker verifies the data for the Hasse-bound primality argument: a
nonsingular curve modulo the candidate integer, a finite point annihilated by
a sufficiently large prime, and a certificate for that prime. Divisions are
justified by supplied modular inverses, each checked by multiplication.

`checkAt n cert` also requires that the certificate is for `n`. The theorem
turning acceptance into `Nat.Prime n` is in `HexECPPMathlib.Soundness`.
-/

namespace Hex.ECPP

/-- Check the elliptic curve conditions that establish `n` prime once `q` is
known prime: a nonsingular short Weierstrass curve, a finite point `(x,y)`,
verified divisions in `q • (x,y) = O`, and a sufficiently large `q < n`.
This function checks the local arithmetic; it does not itself prove `q`
prime. `check` additionally checks the nested certificate for `q`. -/
@[expose]
def checkStep (n a b x y discrInv : Nat) (inverses : List Nat) (q : Nat) : Bool :=
  3 < n && (n % 6 == 1 || n % 6 == 5) &&
    2 ≤ q && q < n &&
    a < n && b < n && x < n && y < n && discrInv < n &&
    onCurve n a b x y &&
    (4 * a * a * a + 27 * b * b) * discrInv % n == 1 &&
    sizeBound n q &&
    replayDone n a b q (.affine x y) inverses

/-- Verify a primality certificate, including every smaller prime it uses.

For an elliptic curve step, verify the curve equation, nonsingularity, the
strict size bound on the auxiliary prime, and scalar multiplication to
infinity using the supplied modular inverses. For a HexPrimality certificate,
use its existing primality checker.

In `HexECPPMathlib`, `natPrime_of_check` proves that a `true` result implies
`Nat.Prime cert.subject`. -/
@[expose]
def check : Cert → Bool
  | .base cert => Hex.Nat.checkPrime cert
  | .step n a b x y discrInv inverses child =>
      check child && checkStep n a b x y discrInv inverses child.subject

/-- Verify that `cert` is a valid primality certificate for the integer `n`.
Return `false` if it records a different integer, even when its own
certificate is valid. In `HexECPPMathlib`, `natPrime_of_checkAt` turns a
`true` result into a theorem of `Nat.Prime n`. -/
@[expose]
def checkAt (n : Nat) (cert : Cert) : Bool :=
  cert.subject == n && check cert

/-- A certificate ending with HexPrimality data is checked by its existing
primality checker. -/
@[simp] theorem check_base (cert : Hex.Nat.PrimeCert) :
    check (.base cert) = Hex.Nat.checkPrime cert := rfl

/-- Checking an elliptic step checks its smaller prime's certificate and
uses exactly that prime as the scalar in the point multiplication. -/
theorem check_step (n a b x y d : Nat) (ws : List Nat) (child : Cert) :
    check (.step n a b x y d ws child) =
      (check child && checkStep n a b x y d ws child.subject) := rfl

/-- Checking a certificate for `n` succeeds exactly when its recorded integer
is `n` and the certificate itself passes the primality checker. -/
@[simp] theorem checkAt_eq_true_iff {n : Nat} {cert : Cert} :
    checkAt n cert = true ↔ cert.subject = n ∧ check cert = true := by
  simp [checkAt]

/-- Accepted step data uses canonical curve, point and discriminant residues. -/
theorem checkStep_canonical {n a b x y discrInv q : Nat}
    {inverses : List Nat}
    (h : checkStep n a b x y discrInv inverses q = true) :
    a < n ∧ b < n ∧ x < n ∧ y < n ∧ discrInv < n := by
  simp only [checkStep, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_iff, beq_iff_eq] at h
  grind

/-- An accepted step satisfies the curve, inverse and size conditions, and
its scalar multiplication reaches infinity with no unused inverse witnesses. -/
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

/-- A certificate accepted for `n` records `n` as its intended prime. -/
theorem checkAt_subject {n : Nat} {cert : Cert}
    (h : checkAt n cert = true) : cert.subject = n := by
  simp only [checkAt, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- A certificate accepted for `n` also passes the certificate checker alone. -/
theorem checkAt_check {n : Nat} {cert : Cert}
    (h : checkAt n cert = true) : check cert = true := by
  simp only [checkAt, Bool.and_eq_true] at h
  exact h.2

end Hex.ECPP
