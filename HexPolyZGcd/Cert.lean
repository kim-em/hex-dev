/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModArith.Modulus
public import HexPolyFp
public import HexPolyZ.Kronecker
public import HexPolyZGcd.Divide

public section
set_option backward.proofsInPublic true

/-!
Checked certificates for integer-polynomial gcd candidates.

Candidate production is deliberately kept out of this file.  The checker only
replays two exact product identities, normalization, coprime integer contents,
and one of two independently checkable coprimality witnesses.
-/

namespace Hex

namespace ZPoly

/-- Coefficientwise reduction of an integer polynomial into a bundled
word-sized residue ring.  This copy is local to the gcd checker so its kernel
closure does not depend on the Hensel implementation. -/
@[expose]
def reduceModP (p : Nat) [ZMod64.Bounds p] (f : ZPoly) : FpPoly p :=
  DensePoly.ofList <|
    (List.range f.size).map (fun i => ZMod64.intCast p (f.coeff i))

/-- Evidence that the two cofactors have no common nonunit factor. -/
inductive CoprimeWitness
  /-- A degree-preserving reduction and a Bezout identity over a prime field. -/
  | modular (p : ZMod64.Prime)
      (alpha beta : @FpPoly p.m p.bounds)
  /-- An integral polynomial combination equal to a nonzero constant. -/
  | constant (u v : ZPoly) (k : Int)

/-- A gcd candidate, its two exact cofactors, and checked coprimality data. -/
structure GcdCert where
  gcd : ZPoly
  cofL : ZPoly
  cofR : ZPoly
  coprime : CoprimeWitness

/-- The normalization convention for integer gcds.  Zero is admitted for the
unique degenerate answer `gcd 0 0`; every nonzero result has positive leading
coefficient and positive content. -/
@[expose]
def NormalizedGcd (g : ZPoly) : Bool :=
  g == 0 ||
    (decide (0 < DensePoly.leadingCoeff g) && decide (0 < content g))

/-- Check a dense integer-polynomial product by one Kronecker evaluation.

The slot width covers both the convolution bound and every target coefficient,
so equality of the packed integers is equality coefficient by coefficient.
Unlike materialising `p * q` through either schoolbook convolution or
Kronecker unpacking, the checker needs no result polynomial: it packs the
target once and compares the two integers directly. -/
@[expose]
def mulEqPacked (p q target : ZPoly) : Bool :=
  if p.isZero || q.isZero then
    target == 0
  else
    let slots := p.size + q.size - 1
    let width := bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target))
    let b := 2 * width + ceilLog2 (min p.size q.size) + 1
    let bias : Int := Int.ofNat (2 ^ (b - 1))
    decide (target.size ≤ slots) &&
      (packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
          constPack b bias slots ==
        packAux b (fun i => target.coeff i + bias) 0 slots)

/-- Packing a target with the Kronecker bias is the same integer that the
ordinary Kronecker product kernel would unpack for `target * 1`. -/
private theorem packTarget (target : ZPoly) (b slots : Nat)
    (hsize : target.size ≤ slots) :
    let bias : Int := ((2 ^ (b - 1) : Nat) : Int)
    packAux b (fun i => target.coeff i + bias) 0 slots =
      packAux b target.coeff 0 target.size *
          packAux b (1 : ZPoly).coeff 0 (1 : ZPoly).size +
        constPack b bias slots := by
  dsimp only
  rw [packAux_eq, packAux_eq, packAux_eq, constPack_eq]
  simp only [Nat.zero_add]
  rw [packSpec_add_fun, packSpec_eq_eval b target slots hsize,
    packSpec_eq_eval b target target.size (Nat.le_refl _),
    packSpec_eq_eval b (1 : ZPoly) (1 : ZPoly).size (Nat.le_refl _)]
  have hone : DensePoly.eval (1 : ZPoly) ((2 : Int) ^ b) = 1 := by
    change DensePoly.eval (DensePoly.C (1 : Int)) ((2 : Int) ^ b) = 1
    exact DensePoly.eval_C_semiring 1 ((2 : Int) ^ b)
  rw [hone, Int.mul_one]

/-- A successful packed multiplication comparison is an exact polynomial
identity. -/
theorem mulEqPacked_sound {p q target : ZPoly}
    (hcheck : mulEqPacked p q target = true) :
    p * q = target := by
  unfold mulEqPacked at hcheck
  by_cases hz : p.isZero || q.isZero
  · rw [if_pos hz] at hcheck
    have htarget : target = 0 := by
      simpa [beq_iff_eq] using hcheck
    have hz' : p.isZero = true ∨ q.isZero = true := by
      simpa only [Bool.or_eq_true] using hz
    rcases hz' with hp | hq
    · have hp0 : p = 0 :=
        (DensePoly.size_eq_zero_iff p).mp ((DensePoly.isZero_eq_true_iff p).mp hp)
      rw [hp0, htarget]
      exact DensePoly.zero_mul q
    · have hq0 : q = 0 :=
        (DensePoly.size_eq_zero_iff q).mp ((DensePoly.isZero_eq_true_iff q).mp hq)
      rw [hq0, htarget, DensePoly.mul_comm_poly]
      exact DensePoly.zero_mul p
  · rw [if_neg hz] at hcheck
    dsimp only at hcheck
    have hparts :
        target.size ≤ p.size + q.size - 1 ∧
          packAux
                (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1)
                p.coeff 0 p.size *
              packAux
                (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1)
                q.coeff 0 q.size +
              constPack
                (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1)
                (Int.ofNat
                  (2 ^ (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1 - 1)))
                (p.size + q.size - 1) =
            packAux
              (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                  ceilLog2 (min p.size q.size) + 1)
              (fun i => target.coeff i +
                Int.ofNat
                  (2 ^ (2 * bitLen (max (max (maxAbs p) (maxAbs q)) (maxAbs target)) +
                    ceilLog2 (min p.size q.size) + 1 - 1)))
              0 (p.size + q.size - 1) := by
      simpa [Bool.and_eq_true, beq_iff_eq] using hcheck
    let A := max (max (maxAbs p) (maxAbs q)) (maxAbs target)
    let width := bitLen A
    let b := 2 * width + ceilLog2 (min p.size q.size) + 1
    let slots := p.size + q.size - 1
    have hsize : target.size ≤ slots := by
      simpa [slots] using hparts.1
    have hpack :
        packAux b p.coeff 0 p.size * packAux b q.coeff 0 q.size +
            constPack b (((2 ^ (b - 1) : Nat) : Int)) slots =
          packAux b (fun i => target.coeff i + ((2 ^ (b - 1) : Nat) : Int)) 0 slots := by
      simpa [A, width, b, slots] using hparts.2
    have hb : 0 < b := by
      simp only [b]
      omega
    have hpBound : ∀ i, (p.coeff i).natAbs ≤ A := fun i =>
      Nat.le_trans (natAbs_coeff_le_maxAbs p i)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    have hqBound : ∀ i, (q.coeff i).natAbs ≤ A := fun i =>
      Nat.le_trans (natAbs_coeff_le_maxAbs q i)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    have hproductBudget : ∀ n, ((p * q).coeff n).natAbs < 2 ^ (b - 1) := by
      intro n
      have hle := natAbs_coeff_mul_le_min p q A hpBound hqBound n
      have hpow : (2 : Nat) ^ (b - 1) =
          2 ^ ceilLog2 (min p.size q.size) * (2 ^ width * 2 ^ width) := by
        rw [show b - 1 = ceilLog2 (min p.size q.size) + (width + width) by
          simp only [b]
          omega, Nat.pow_add, Nat.pow_add]
      have hA : A < 2 ^ width := by
        simpa only [width] using lt_two_pow_bitLen A
      have hxpos : 0 < 2 ^ width := Nat.two_pow_pos _
      have haa : A * A < 2 ^ width * 2 ^ width := by
        have h1 : A * A ≤ A * 2 ^ width :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt hA)
        have h2 : A * 2 ^ width < 2 ^ width * 2 ^ width :=
          (Nat.mul_lt_mul_right hxpos).mpr hA
        omega
      have hMpos : 0 < 2 ^ ceilLog2 (min p.size q.size) := Nat.two_pow_pos _
      have h3 : min p.size q.size * (A * A) ≤
          2 ^ ceilLog2 (min p.size q.size) * (A * A) :=
        Nat.mul_le_mul_right _ (le_two_pow_ceilLog2 _)
      have h4 : 2 ^ ceilLog2 (min p.size q.size) * (A * A) <
          2 ^ ceilLog2 (min p.size q.size) * (2 ^ width * 2 ^ width) :=
        (Nat.mul_lt_mul_left hMpos).mpr haa
      omega
    have htargetBudget : ∀ n, (target.coeff n).natAbs < 2 ^ (b - 1) := by
      intro n
      have hcoeff : (target.coeff n).natAbs ≤ A :=
        Nat.le_trans (natAbs_coeff_le_maxAbs target n) (Nat.le_max_right _ _)
      have hA : A < 2 ^ width := by
        simpa only [width] using lt_two_pow_bitLen A
      have hexp : width ≤ b - 1 := by
        simp only [b]
        omega
      exact Nat.lt_of_le_of_lt hcoeff <|
        Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)
    have hproduct := kronecker_identity p q b slots hb
      (by simpa only [slots] using DensePoly.size_mul_le p q) hproductBudget
    have htarget := kronecker_identity target (1 : ZPoly) b slots hb
      (by simpa only [DensePoly.mul_one_right_poly] using hsize)
      (by
        intro n
        simpa only [DensePoly.mul_one_right_poly] using htargetBudget n)
    rw [hpack, packTarget target b slots hsize] at hproduct
    rw [DensePoly.mul_one_right_poly] at htarget
    exact hproduct.symm.trans htarget

/-- Replay the coprimality half of a gcd certificate. -/
@[expose]
def checkCoprime (f h : ZPoly) : CoprimeWitness → Bool
  | .constant u v k =>
      decide (k ≠ 0) && (u * f + v * h == DensePoly.C k)
  | .modular p alpha beta =>
      letI : ZMod64.Bounds p.m := p.bounds
      letI : ZMod64.PrimeModulus p.m := ZMod64.primeModulusOfPrime p.prime
      let fp := reduceModP p.m f
      let hp := reduceModP p.m h
      decide (fp.size = f.size) &&
        decide (hp.size = h.size) &&
        (alpha * fp + beta * hp == 1)

/-- Check a gcd certificate.  Every producer, including deterministic
fallbacks, must pass through this function before its candidate is exposed. -/
@[expose]
def checkGcd (f h : ZPoly) (c : GcdCert) : Bool :=
  mulEqPacked c.gcd c.cofL f &&
    mulEqPacked c.gcd c.cofR h &&
    NormalizedGcd c.gcd &&
    decide (Int.gcd (content c.cofL) (content c.cofR) = 1) &&
    checkCoprime c.cofL c.cofR c.coprime

/-- The cofactor identities together with absence of a common nonunit
cofactor. -/
def CoprimeCofactors (f h g : ZPoly) : Prop :=
  ∃ f' h', f = g * f' ∧ h = g * h' ∧
    ∀ d : ZPoly, d ∣ f' → d ∣ h' → IsUnit d

/-- A successful checker establishes both exact cofactor identities and
coprimality of the cofactors. -/
theorem checkGcd_sound {f h : ZPoly} {c : GcdCert}
    (hc : checkGcd f h c = true) :
    f = c.gcd * c.cofL ∧ h = c.gcd * c.cofR ∧
      ∀ d : ZPoly, d ∣ c.cofL → d ∣ c.cofR → IsUnit d := by
  sorry

/-- Checker soundness packaged in the public cofactor predicate. -/
theorem coprimeCofactors_of_checkGcd {f h : ZPoly} {c : GcdCert}
    (hc : checkGcd f h c = true) :
    CoprimeCofactors f h c.gcd := by
  rcases checkGcd_sound hc with ⟨hf, hh, hcop⟩
  exact ⟨c.cofL, c.cofR, hf, hh, hcop⟩

end ZPoly

end Hex
