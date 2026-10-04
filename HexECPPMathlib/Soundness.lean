/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Reduction
public import HexECPPMathlib.Order
public import HexPrimalityMathlib.Prime

/-!
# Why accepted elliptic curve certificates prove primality

For every prime divisor `p` of the candidate integer `n`, an accepted
certificate gives a nonidentity point on an elliptic curve over `ZMod p`
annihilated by the auxiliary prime `q`. Its order is exactly `q`, so Hasse's
bound excludes `p ≤ √n` once the certificate's size inequality holds.
This rules out compositeness. Recursion checks the primality certificate
for `q` and ultimately reduces to HexPrimality's existing soundness theorem.

`natPrime_of_checkAt` has just the checker equation as its premise. Curve
orders proposed during search, random choices, and external programs are not
assumptions of the resulting `Nat.Prime n` theorem.
-/

@[expose] public section

namespace Hex.ECPP

/-- The structurally recursive raw replay computes the canonical binary
prefix of the scalar in the actual elliptic-curve group. -/
theorem replayBits_rep {p n a b q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (Q : Point) (V : (shortCurve p a b).toAffine.Point)
    (hQ : Q.Rep p a b V) :
    ∀ (k : ℕ) {R S : Point} {ws rest : List ℕ}
      (U : (shortCurve p a b).toAffine.Point),
      R.Rep p a b U → replayBits n a b q Q k R ws = some (S, rest) →
      S.Rep p a b ((2 ^ k) • U + (q % 2 ^ k) • V)
  | 0, R, S, ws, rest, U, hR, h => by
      simp only [replayBits, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [Nat.mod_one] using hR
  | k + 1, R, S, ws, rest, U, hR, h => by
      cases hD : checkedAdd? n a b R R ws with
      | none => simp [replayBits, hD] at h
      | some pair =>
        rcases pair with ⟨D, ws₁⟩
        have hDrep := add_rep hp hn hR hR (checkedAdd_facts hD).1
        cases hbit : q.testBit k with
        | false =>
          have hrec : replayBits n a b q Q k D ws₁ = some (S, rest) := by
            simpa [replayBits, hD, hbit] using h
          have hrecRep := replayBits_rep hp hn Q V hQ k (U + U) hDrep hrec
          have hscalar : (2 ^ k) • (U + U) + (q % 2 ^ k) • V =
              (2 ^ (k + 1)) • U + (q % 2 ^ (k + 1)) • V := by
            rw [bit_mod_succ]
            simp [hbit, pow_succ, mul_nsmul, nsmul_add, two_nsmul]
          rw [← hscalar]
          exact hrecRep
        | true =>
          cases hT : checkedAdd? n a b D Q ws₁ with
          | none => simp [replayBits, hD, hbit, hT] at h
          | some pair =>
            rcases pair with ⟨T, ws₂⟩
            have hrec : replayBits n a b q Q k T ws₂ = some (S, rest) := by
              simpa [replayBits, hD, hbit, hT] using h
            have hTrep := add_rep hp hn hDrep hQ (checkedAdd_facts hT).1
            have hrecRep := replayBits_rep hp hn Q V hQ k
              ((U + U) + V) hTrep hrec
            have hscalar : (2 ^ k) • ((U + U) + V) + (q % 2 ^ k) • V =
                (2 ^ (k + 1)) • U + (q % 2 ^ (k + 1)) • V := by
              rw [bit_mod_succ]
              simp [hbit, pow_succ, mul_nsmul, nsmul_add, add_nsmul, two_nsmul]
              abel
            rw [← hscalar]
            exact hrecRep

/-- If the complete replay returns infinity, its field point is annihilated
by the child subject. -/
theorem replay_zero {p n a b q : ℕ} [Fact p.Prime] (hp : p ∣ n) (hn : 0 < n)
    (Q : Point) (V : (shortCurve p a b).toAffine.Point)
    (hQ : Q.Rep p a b V) {ws rest : List ℕ}
    (h : replay n a b q Q ws = some (.infinity, rest)) : q • V = 0 := by
  have hrep := replayBits_rep hp hn Q V hQ (HexArith.bitLength q)
    (R := .infinity) (S := .infinity) (ws := ws) (rest := rest)
    0 (by rfl) h
  change (2 ^ HexArith.bitLength q) • (0 : (shortCurve p a b).toAffine.Point) +
    (q % 2 ^ HexArith.bitLength q) • V = 0 at hrep
  simpa [Nat.mod_eq_of_lt (HexArith.lt_two_pow_bitLength q)] using hrep

set_option linter.style.haveILetI false in
/-- A checked ECPP step is prime once its structurally smaller child subject
is prime. No primality of the candidate is assumed. -/
theorem natPrime_of_step {n a b x y discrInv q : ℕ} {inverses : List ℕ}
    (hq : q.Prime)
    (h : checkStep n a b x y discrInv inverses q = true) : n.Prime := by
  obtain ⟨hn3, hmod, _, _, hcurve, hdisc, hsize, hreplay⟩ := checkStep_facts h
  by_contra hnp
  let p := Nat.minFac n
  have hpPrime : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hpDiv : p ∣ n := Nat.minFac_dvd n
  have hpSq : p * p ≤ n := by
    simpa only [pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hnp
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hp3 : 3 < p := prime_divisor_gt_three hpPrime hpDiv hmod
  letI : (shortCurve p a b).toAffine.IsElliptic :=
    shortCurve_elliptic hpPrime hp3 hpDiv hdisc
  obtain ⟨P, hP, hP0⟩ := startingPoint_rep hpPrime hp3 hpDiv hdisc hcurve
  have hzero : q • P = 0 := replay_zero hpDiv (by omega) _ P hP hreplay
  have horder : q ≤ Fintype.card (shortCurve p a b).toAffine.Point :=
    prime_order_le_card hq hP0 hzero
  have hhasse := hasse_sq_zmod p (shortCurve p a b)
  exact size_excludes_small_divisor p n q
    (Fintype.card (shortCurve p a b).toAffine.Point) hq.two_le
    hpSq horder hhasse hsize

/-- An accepted elliptic curve primality certificate proves its recorded
integer prime in Mathlib. The sole premise is the checker equation:
the smaller primes, curve nonsingularity, point order and Hasse-bound size
condition are all verified by the certificate and soundness proof. -/
theorem natPrime_of_check {cert : Cert} (h : check cert = true) :
    _root_.Nat.Prime cert.subject := by
  induction cert with
  | base c =>
      simpa only [Cert.subject, check] using Hex.Nat.natPrime_of_checkPrime h
  | step n a b x y discrInv inverses child ih =>
      change (check child && checkStep n a b x y discrInv inverses child.subject) = true at h
      rw [Bool.and_eq_true] at h
      have hchild : check child = true := by
        exact h.1
      have hstep : checkStep n a b x y discrInv inverses child.subject = true := by
        exact h.2
      simpa only [Cert.subject] using natPrime_of_step (ih hchild) hstep

/-- If `checkAt n cert = true`, then `n` is prime. The checker verifies both
the certificate and that its recorded integer is `n`; no additional
assumption about search, curve orders or auxiliary primes is required. -/
theorem natPrime_of_checkAt {n : ℕ} {cert : Cert}
    (h : checkAt n cert = true) : _root_.Nat.Prime n := by
  rw [← checkAt_subject h]
  exact natPrime_of_check (checkAt_check h)

end Hex.ECPP
